%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:22 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.68s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 187 expanded)
%              Number of leaves         :   37 (  81 expanded)
%              Depth                    :    8
%              Number of atoms          :  120 ( 453 expanded)
%              Number of equality atoms :   30 ( 124 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_9 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_9',type,(
    '#skF_9': $i > $i )).

tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_112,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] :
                    ~ ( r2_hidden(E,A)
                      & D = k1_funct_1(C,E) ) )
         => k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_60,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_231,plain,(
    ! [A_115,B_116,C_117] :
      ( k2_relset_1(A_115,B_116,C_117) = k2_relat_1(C_117)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_240,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_60,c_231])).

tff(c_58,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_241,plain,(
    k2_relat_1('#skF_8') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_58])).

tff(c_287,plain,(
    ! [A_127,B_128,C_129] :
      ( m1_subset_1(k2_relset_1(A_127,B_128,C_129),k1_zfmisc_1(B_128))
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_311,plain,
    ( m1_subset_1(k2_relat_1('#skF_8'),k1_zfmisc_1('#skF_7'))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_287])).

tff(c_317,plain,(
    m1_subset_1(k2_relat_1('#skF_8'),k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_311])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,B_10)
      | ~ m1_subset_1(A_9,k1_zfmisc_1(B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_321,plain,(
    r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_317,c_16])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_334,plain,
    ( k2_relat_1('#skF_8') = '#skF_7'
    | ~ r1_tarski('#skF_7',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_321,c_8])).

tff(c_338,plain,(
    ~ r1_tarski('#skF_7',k2_relat_1('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_241,c_334])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_62,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_174,plain,(
    ! [A_102,B_103,C_104] :
      ( k1_relset_1(A_102,B_103,C_104) = k1_relat_1(C_104)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_183,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_60,c_174])).

tff(c_1366,plain,(
    ! [B_239,A_240,C_241] :
      ( k1_xboole_0 = B_239
      | k1_relset_1(A_240,B_239,C_241) = A_240
      | ~ v1_funct_2(C_241,A_240,B_239)
      | ~ m1_subset_1(C_241,k1_zfmisc_1(k2_zfmisc_1(A_240,B_239))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1381,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_1366])).

tff(c_1388,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_183,c_1381])).

tff(c_1389,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1388])).

tff(c_68,plain,(
    ! [D_69] :
      ( r2_hidden('#skF_9'(D_69),'#skF_6')
      | ~ r2_hidden(D_69,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_154,plain,(
    ! [C_94,B_95,A_96] :
      ( r2_hidden(C_94,B_95)
      | ~ r2_hidden(C_94,A_96)
      | ~ r1_tarski(A_96,B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_160,plain,(
    ! [D_69,B_95] :
      ( r2_hidden('#skF_9'(D_69),B_95)
      | ~ r1_tarski('#skF_6',B_95)
      | ~ r2_hidden(D_69,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_68,c_154])).

tff(c_93,plain,(
    ! [C_81,A_82,B_83] :
      ( v1_relat_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_102,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_60,c_93])).

tff(c_64,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_66,plain,(
    ! [D_69] :
      ( k1_funct_1('#skF_8','#skF_9'(D_69)) = D_69
      | ~ r2_hidden(D_69,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_322,plain,(
    ! [A_130,D_131] :
      ( r2_hidden(k1_funct_1(A_130,D_131),k2_relat_1(A_130))
      | ~ r2_hidden(D_131,k1_relat_1(A_130))
      | ~ v1_funct_1(A_130)
      | ~ v1_relat_1(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_327,plain,(
    ! [D_69] :
      ( r2_hidden(D_69,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_9'(D_69),k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_69,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_322])).

tff(c_346,plain,(
    ! [D_134] :
      ( r2_hidden(D_134,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_9'(D_134),k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_134,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_64,c_327])).

tff(c_351,plain,(
    ! [D_69] :
      ( r2_hidden(D_69,k2_relat_1('#skF_8'))
      | ~ r1_tarski('#skF_6',k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_69,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_160,c_346])).

tff(c_471,plain,(
    ~ r1_tarski('#skF_6',k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_351])).

tff(c_1390,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1389,c_471])).

tff(c_1395,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1390])).

tff(c_1396,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_1388])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1431,plain,(
    ! [A_8] : r1_tarski('#skF_7',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1396,c_14])).

tff(c_1440,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1431,c_338])).

tff(c_1451,plain,(
    ! [D_242] :
      ( r2_hidden(D_242,k2_relat_1('#skF_8'))
      | ~ r2_hidden(D_242,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_351])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1514,plain,(
    ! [A_249] :
      ( r1_tarski(A_249,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_1'(A_249,k2_relat_1('#skF_8')),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1451,c_4])).

tff(c_1522,plain,(
    r1_tarski('#skF_7',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_6,c_1514])).

tff(c_1527,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_338,c_338,c_1522])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:04:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.32/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.63  
% 3.32/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.63  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_9 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 3.32/1.63  
% 3.32/1.63  %Foreground sorts:
% 3.32/1.63  
% 3.32/1.63  
% 3.32/1.63  %Background operators:
% 3.32/1.63  
% 3.32/1.63  
% 3.32/1.63  %Foreground operators:
% 3.32/1.63  tff('#skF_9', type, '#skF_9': $i > $i).
% 3.32/1.63  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.32/1.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.32/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.32/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.32/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.32/1.63  tff('#skF_7', type, '#skF_7': $i).
% 3.32/1.63  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.32/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.32/1.63  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.32/1.63  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.32/1.63  tff('#skF_6', type, '#skF_6': $i).
% 3.32/1.63  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.32/1.63  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.32/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.32/1.63  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.32/1.63  tff('#skF_8', type, '#skF_8': $i).
% 3.32/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.32/1.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.32/1.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.32/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.32/1.63  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.32/1.63  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.32/1.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.32/1.63  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.32/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.32/1.63  
% 3.68/1.64  tff(f_112, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_2)).
% 3.68/1.64  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.68/1.64  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.68/1.64  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.68/1.64  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.68/1.64  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.68/1.64  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.68/1.64  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.68/1.64  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.68/1.64  tff(f_59, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 3.68/1.64  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.68/1.64  tff(c_60, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.68/1.64  tff(c_231, plain, (![A_115, B_116, C_117]: (k2_relset_1(A_115, B_116, C_117)=k2_relat_1(C_117) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.68/1.64  tff(c_240, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_60, c_231])).
% 3.68/1.64  tff(c_58, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.68/1.64  tff(c_241, plain, (k2_relat_1('#skF_8')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_240, c_58])).
% 3.68/1.64  tff(c_287, plain, (![A_127, B_128, C_129]: (m1_subset_1(k2_relset_1(A_127, B_128, C_129), k1_zfmisc_1(B_128)) | ~m1_subset_1(C_129, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.68/1.64  tff(c_311, plain, (m1_subset_1(k2_relat_1('#skF_8'), k1_zfmisc_1('#skF_7')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_240, c_287])).
% 3.68/1.64  tff(c_317, plain, (m1_subset_1(k2_relat_1('#skF_8'), k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_311])).
% 3.68/1.64  tff(c_16, plain, (![A_9, B_10]: (r1_tarski(A_9, B_10) | ~m1_subset_1(A_9, k1_zfmisc_1(B_10)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.68/1.64  tff(c_321, plain, (r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_317, c_16])).
% 3.68/1.64  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.68/1.64  tff(c_334, plain, (k2_relat_1('#skF_8')='#skF_7' | ~r1_tarski('#skF_7', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_321, c_8])).
% 3.68/1.64  tff(c_338, plain, (~r1_tarski('#skF_7', k2_relat_1('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_241, c_334])).
% 3.68/1.64  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.68/1.64  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.68/1.64  tff(c_62, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.68/1.64  tff(c_174, plain, (![A_102, B_103, C_104]: (k1_relset_1(A_102, B_103, C_104)=k1_relat_1(C_104) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.68/1.64  tff(c_183, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_60, c_174])).
% 3.68/1.64  tff(c_1366, plain, (![B_239, A_240, C_241]: (k1_xboole_0=B_239 | k1_relset_1(A_240, B_239, C_241)=A_240 | ~v1_funct_2(C_241, A_240, B_239) | ~m1_subset_1(C_241, k1_zfmisc_1(k2_zfmisc_1(A_240, B_239))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.68/1.64  tff(c_1381, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_60, c_1366])).
% 3.68/1.64  tff(c_1388, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_183, c_1381])).
% 3.68/1.64  tff(c_1389, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_1388])).
% 3.68/1.64  tff(c_68, plain, (![D_69]: (r2_hidden('#skF_9'(D_69), '#skF_6') | ~r2_hidden(D_69, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.68/1.64  tff(c_154, plain, (![C_94, B_95, A_96]: (r2_hidden(C_94, B_95) | ~r2_hidden(C_94, A_96) | ~r1_tarski(A_96, B_95))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.68/1.64  tff(c_160, plain, (![D_69, B_95]: (r2_hidden('#skF_9'(D_69), B_95) | ~r1_tarski('#skF_6', B_95) | ~r2_hidden(D_69, '#skF_7'))), inference(resolution, [status(thm)], [c_68, c_154])).
% 3.68/1.64  tff(c_93, plain, (![C_81, A_82, B_83]: (v1_relat_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.68/1.64  tff(c_102, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_60, c_93])).
% 3.68/1.64  tff(c_64, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.68/1.64  tff(c_66, plain, (![D_69]: (k1_funct_1('#skF_8', '#skF_9'(D_69))=D_69 | ~r2_hidden(D_69, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.68/1.64  tff(c_322, plain, (![A_130, D_131]: (r2_hidden(k1_funct_1(A_130, D_131), k2_relat_1(A_130)) | ~r2_hidden(D_131, k1_relat_1(A_130)) | ~v1_funct_1(A_130) | ~v1_relat_1(A_130))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.68/1.64  tff(c_327, plain, (![D_69]: (r2_hidden(D_69, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_9'(D_69), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_69, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_66, c_322])).
% 3.68/1.64  tff(c_346, plain, (![D_134]: (r2_hidden(D_134, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_9'(D_134), k1_relat_1('#skF_8')) | ~r2_hidden(D_134, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_64, c_327])).
% 3.68/1.64  tff(c_351, plain, (![D_69]: (r2_hidden(D_69, k2_relat_1('#skF_8')) | ~r1_tarski('#skF_6', k1_relat_1('#skF_8')) | ~r2_hidden(D_69, '#skF_7'))), inference(resolution, [status(thm)], [c_160, c_346])).
% 3.68/1.64  tff(c_471, plain, (~r1_tarski('#skF_6', k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_351])).
% 3.68/1.64  tff(c_1390, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1389, c_471])).
% 3.68/1.64  tff(c_1395, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_1390])).
% 3.68/1.64  tff(c_1396, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_1388])).
% 3.68/1.64  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.68/1.64  tff(c_1431, plain, (![A_8]: (r1_tarski('#skF_7', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_1396, c_14])).
% 3.68/1.64  tff(c_1440, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1431, c_338])).
% 3.68/1.64  tff(c_1451, plain, (![D_242]: (r2_hidden(D_242, k2_relat_1('#skF_8')) | ~r2_hidden(D_242, '#skF_7'))), inference(splitRight, [status(thm)], [c_351])).
% 3.68/1.64  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.68/1.64  tff(c_1514, plain, (![A_249]: (r1_tarski(A_249, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_1'(A_249, k2_relat_1('#skF_8')), '#skF_7'))), inference(resolution, [status(thm)], [c_1451, c_4])).
% 3.68/1.64  tff(c_1522, plain, (r1_tarski('#skF_7', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_6, c_1514])).
% 3.68/1.64  tff(c_1527, plain, $false, inference(negUnitSimplification, [status(thm)], [c_338, c_338, c_1522])).
% 3.68/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.68/1.64  
% 3.68/1.64  Inference rules
% 3.68/1.64  ----------------------
% 3.68/1.64  #Ref     : 0
% 3.68/1.64  #Sup     : 283
% 3.68/1.64  #Fact    : 0
% 3.68/1.64  #Define  : 0
% 3.68/1.64  #Split   : 13
% 3.68/1.64  #Chain   : 0
% 3.68/1.64  #Close   : 0
% 3.68/1.64  
% 3.68/1.64  Ordering : KBO
% 3.68/1.64  
% 3.68/1.64  Simplification rules
% 3.68/1.64  ----------------------
% 3.68/1.64  #Subsume      : 29
% 3.68/1.64  #Demod        : 274
% 3.68/1.64  #Tautology    : 114
% 3.68/1.64  #SimpNegUnit  : 6
% 3.68/1.64  #BackRed      : 44
% 3.68/1.64  
% 3.68/1.64  #Partial instantiations: 0
% 3.68/1.64  #Strategies tried      : 1
% 3.68/1.64  
% 3.68/1.64  Timing (in seconds)
% 3.68/1.64  ----------------------
% 3.68/1.65  Preprocessing        : 0.34
% 3.68/1.65  Parsing              : 0.18
% 3.68/1.65  CNF conversion       : 0.03
% 3.68/1.65  Main loop            : 0.49
% 3.68/1.65  Inferencing          : 0.17
% 3.68/1.65  Reduction            : 0.16
% 3.68/1.65  Demodulation         : 0.11
% 3.68/1.65  BG Simplification    : 0.03
% 3.68/1.65  Subsumption          : 0.10
% 3.68/1.65  Abstraction          : 0.02
% 3.68/1.65  MUC search           : 0.00
% 3.68/1.65  Cooper               : 0.00
% 3.68/1.65  Total                : 0.87
% 3.68/1.65  Index Insertion      : 0.00
% 3.68/1.65  Index Deletion       : 0.00
% 3.68/1.65  Index Matching       : 0.00
% 3.68/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
