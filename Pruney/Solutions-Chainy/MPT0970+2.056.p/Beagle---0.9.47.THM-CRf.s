%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:27 EST 2020

% Result     : Theorem 3.92s
% Output     : CNFRefutation 3.92s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 193 expanded)
%              Number of leaves         :   38 (  83 expanded)
%              Depth                    :    9
%              Number of atoms          :  126 ( 465 expanded)
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

tff(f_117,negated_conjecture,(
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

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_72,axiom,(
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

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_98,axiom,(
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

tff(f_53,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_68,axiom,(
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

tff(c_62,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_170,plain,(
    ! [A_97,B_98,C_99] :
      ( k2_relset_1(A_97,B_98,C_99) = k2_relat_1(C_99)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_179,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_62,c_170])).

tff(c_60,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_180,plain,(
    k2_relat_1('#skF_8') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_60])).

tff(c_296,plain,(
    ! [A_127,B_128,C_129] :
      ( m1_subset_1(k2_relset_1(A_127,B_128,C_129),k1_zfmisc_1(B_128))
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_319,plain,
    ( m1_subset_1(k2_relat_1('#skF_8'),k1_zfmisc_1('#skF_7'))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_296])).

tff(c_325,plain,(
    m1_subset_1(k2_relat_1('#skF_8'),k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_319])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,B_10)
      | ~ m1_subset_1(A_9,k1_zfmisc_1(B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_333,plain,(
    r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_325,c_16])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_340,plain,
    ( k2_relat_1('#skF_8') = '#skF_7'
    | ~ r1_tarski('#skF_7',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_333,c_8])).

tff(c_345,plain,(
    ~ r1_tarski('#skF_7',k2_relat_1('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_180,c_340])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_64,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_232,plain,(
    ! [A_113,B_114,C_115] :
      ( k1_relset_1(A_113,B_114,C_115) = k1_relat_1(C_115)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_241,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_62,c_232])).

tff(c_2023,plain,(
    ! [B_309,A_310,C_311] :
      ( k1_xboole_0 = B_309
      | k1_relset_1(A_310,B_309,C_311) = A_310
      | ~ v1_funct_2(C_311,A_310,B_309)
      | ~ m1_subset_1(C_311,k1_zfmisc_1(k2_zfmisc_1(A_310,B_309))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2038,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_62,c_2023])).

tff(c_2045,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_241,c_2038])).

tff(c_2046,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_2045])).

tff(c_70,plain,(
    ! [D_71] :
      ( r2_hidden('#skF_9'(D_71),'#skF_6')
      | ~ r2_hidden(D_71,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_163,plain,(
    ! [C_94,B_95,A_96] :
      ( r2_hidden(C_94,B_95)
      | ~ r2_hidden(C_94,A_96)
      | ~ r1_tarski(A_96,B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_169,plain,(
    ! [D_71,B_95] :
      ( r2_hidden('#skF_9'(D_71),B_95)
      | ~ r1_tarski('#skF_6',B_95)
      | ~ r2_hidden(D_71,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_70,c_163])).

tff(c_22,plain,(
    ! [A_14,B_15] : v1_relat_1(k2_zfmisc_1(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_116,plain,(
    ! [B_89,A_90] :
      ( v1_relat_1(B_89)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(A_90))
      | ~ v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_122,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_62,c_116])).

tff(c_126,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_122])).

tff(c_66,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_68,plain,(
    ! [D_71] :
      ( k1_funct_1('#skF_8','#skF_9'(D_71)) = D_71
      | ~ r2_hidden(D_71,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1071,plain,(
    ! [A_209,D_210] :
      ( r2_hidden(k1_funct_1(A_209,D_210),k2_relat_1(A_209))
      | ~ r2_hidden(D_210,k1_relat_1(A_209))
      | ~ v1_funct_1(A_209)
      | ~ v1_relat_1(A_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1076,plain,(
    ! [D_71] :
      ( r2_hidden(D_71,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_9'(D_71),k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_71,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_1071])).

tff(c_1109,plain,(
    ! [D_214] :
      ( r2_hidden(D_214,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_9'(D_214),k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_214,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_66,c_1076])).

tff(c_1114,plain,(
    ! [D_71] :
      ( r2_hidden(D_71,k2_relat_1('#skF_8'))
      | ~ r1_tarski('#skF_6',k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_71,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_169,c_1109])).

tff(c_1210,plain,(
    ~ r1_tarski('#skF_6',k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_1114])).

tff(c_2047,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2046,c_1210])).

tff(c_2052,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2047])).

tff(c_2053,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_2045])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2085,plain,(
    ! [A_8] : r1_tarski('#skF_7',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2053,c_14])).

tff(c_2093,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2085,c_345])).

tff(c_2126,plain,(
    ! [D_314] :
      ( r2_hidden(D_314,k2_relat_1('#skF_8'))
      | ~ r2_hidden(D_314,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_1114])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2171,plain,(
    ! [A_319] :
      ( r1_tarski(A_319,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_1'(A_319,k2_relat_1('#skF_8')),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_2126,c_4])).

tff(c_2179,plain,(
    r1_tarski('#skF_7',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_6,c_2171])).

tff(c_2184,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_345,c_345,c_2179])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n017.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:34:16 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.92/1.69  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.92/1.70  
% 3.92/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.92/1.70  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_9 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 3.92/1.70  
% 3.92/1.70  %Foreground sorts:
% 3.92/1.70  
% 3.92/1.70  
% 3.92/1.70  %Background operators:
% 3.92/1.70  
% 3.92/1.70  
% 3.92/1.70  %Foreground operators:
% 3.92/1.70  tff('#skF_9', type, '#skF_9': $i > $i).
% 3.92/1.70  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.92/1.70  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.92/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.92/1.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.92/1.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.92/1.70  tff('#skF_7', type, '#skF_7': $i).
% 3.92/1.70  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.92/1.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.92/1.70  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.92/1.70  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.92/1.70  tff('#skF_6', type, '#skF_6': $i).
% 3.92/1.70  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.92/1.70  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.92/1.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.92/1.70  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.92/1.70  tff('#skF_8', type, '#skF_8': $i).
% 3.92/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.92/1.70  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.92/1.70  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.92/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.92/1.70  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.92/1.70  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.92/1.70  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.92/1.70  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.92/1.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.92/1.70  
% 3.92/1.72  tff(f_117, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_2)).
% 3.92/1.72  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.92/1.72  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.92/1.72  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.92/1.72  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.92/1.72  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.92/1.72  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.92/1.72  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.92/1.72  tff(f_53, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.92/1.72  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.92/1.72  tff(f_68, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 3.92/1.72  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.92/1.72  tff(c_62, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.92/1.72  tff(c_170, plain, (![A_97, B_98, C_99]: (k2_relset_1(A_97, B_98, C_99)=k2_relat_1(C_99) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.92/1.72  tff(c_179, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_62, c_170])).
% 3.92/1.72  tff(c_60, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.92/1.72  tff(c_180, plain, (k2_relat_1('#skF_8')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_179, c_60])).
% 3.92/1.72  tff(c_296, plain, (![A_127, B_128, C_129]: (m1_subset_1(k2_relset_1(A_127, B_128, C_129), k1_zfmisc_1(B_128)) | ~m1_subset_1(C_129, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.92/1.72  tff(c_319, plain, (m1_subset_1(k2_relat_1('#skF_8'), k1_zfmisc_1('#skF_7')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_179, c_296])).
% 3.92/1.72  tff(c_325, plain, (m1_subset_1(k2_relat_1('#skF_8'), k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_319])).
% 3.92/1.72  tff(c_16, plain, (![A_9, B_10]: (r1_tarski(A_9, B_10) | ~m1_subset_1(A_9, k1_zfmisc_1(B_10)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.92/1.72  tff(c_333, plain, (r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_325, c_16])).
% 3.92/1.72  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.92/1.72  tff(c_340, plain, (k2_relat_1('#skF_8')='#skF_7' | ~r1_tarski('#skF_7', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_333, c_8])).
% 3.92/1.72  tff(c_345, plain, (~r1_tarski('#skF_7', k2_relat_1('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_180, c_340])).
% 3.92/1.72  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.92/1.72  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.92/1.72  tff(c_64, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.92/1.72  tff(c_232, plain, (![A_113, B_114, C_115]: (k1_relset_1(A_113, B_114, C_115)=k1_relat_1(C_115) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.92/1.72  tff(c_241, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_62, c_232])).
% 3.92/1.72  tff(c_2023, plain, (![B_309, A_310, C_311]: (k1_xboole_0=B_309 | k1_relset_1(A_310, B_309, C_311)=A_310 | ~v1_funct_2(C_311, A_310, B_309) | ~m1_subset_1(C_311, k1_zfmisc_1(k2_zfmisc_1(A_310, B_309))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.92/1.72  tff(c_2038, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_62, c_2023])).
% 3.92/1.72  tff(c_2045, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_241, c_2038])).
% 3.92/1.72  tff(c_2046, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_2045])).
% 3.92/1.72  tff(c_70, plain, (![D_71]: (r2_hidden('#skF_9'(D_71), '#skF_6') | ~r2_hidden(D_71, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.92/1.72  tff(c_163, plain, (![C_94, B_95, A_96]: (r2_hidden(C_94, B_95) | ~r2_hidden(C_94, A_96) | ~r1_tarski(A_96, B_95))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.92/1.72  tff(c_169, plain, (![D_71, B_95]: (r2_hidden('#skF_9'(D_71), B_95) | ~r1_tarski('#skF_6', B_95) | ~r2_hidden(D_71, '#skF_7'))), inference(resolution, [status(thm)], [c_70, c_163])).
% 3.92/1.72  tff(c_22, plain, (![A_14, B_15]: (v1_relat_1(k2_zfmisc_1(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.92/1.72  tff(c_116, plain, (![B_89, A_90]: (v1_relat_1(B_89) | ~m1_subset_1(B_89, k1_zfmisc_1(A_90)) | ~v1_relat_1(A_90))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.92/1.72  tff(c_122, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_62, c_116])).
% 3.92/1.72  tff(c_126, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_122])).
% 3.92/1.72  tff(c_66, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.92/1.72  tff(c_68, plain, (![D_71]: (k1_funct_1('#skF_8', '#skF_9'(D_71))=D_71 | ~r2_hidden(D_71, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.92/1.72  tff(c_1071, plain, (![A_209, D_210]: (r2_hidden(k1_funct_1(A_209, D_210), k2_relat_1(A_209)) | ~r2_hidden(D_210, k1_relat_1(A_209)) | ~v1_funct_1(A_209) | ~v1_relat_1(A_209))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.92/1.72  tff(c_1076, plain, (![D_71]: (r2_hidden(D_71, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_9'(D_71), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_71, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_1071])).
% 3.92/1.72  tff(c_1109, plain, (![D_214]: (r2_hidden(D_214, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_9'(D_214), k1_relat_1('#skF_8')) | ~r2_hidden(D_214, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_66, c_1076])).
% 3.92/1.72  tff(c_1114, plain, (![D_71]: (r2_hidden(D_71, k2_relat_1('#skF_8')) | ~r1_tarski('#skF_6', k1_relat_1('#skF_8')) | ~r2_hidden(D_71, '#skF_7'))), inference(resolution, [status(thm)], [c_169, c_1109])).
% 3.92/1.72  tff(c_1210, plain, (~r1_tarski('#skF_6', k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_1114])).
% 3.92/1.72  tff(c_2047, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2046, c_1210])).
% 3.92/1.72  tff(c_2052, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_2047])).
% 3.92/1.72  tff(c_2053, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_2045])).
% 3.92/1.72  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.92/1.72  tff(c_2085, plain, (![A_8]: (r1_tarski('#skF_7', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_2053, c_14])).
% 3.92/1.72  tff(c_2093, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2085, c_345])).
% 3.92/1.72  tff(c_2126, plain, (![D_314]: (r2_hidden(D_314, k2_relat_1('#skF_8')) | ~r2_hidden(D_314, '#skF_7'))), inference(splitRight, [status(thm)], [c_1114])).
% 3.92/1.72  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.92/1.72  tff(c_2171, plain, (![A_319]: (r1_tarski(A_319, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_1'(A_319, k2_relat_1('#skF_8')), '#skF_7'))), inference(resolution, [status(thm)], [c_2126, c_4])).
% 3.92/1.72  tff(c_2179, plain, (r1_tarski('#skF_7', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_6, c_2171])).
% 3.92/1.72  tff(c_2184, plain, $false, inference(negUnitSimplification, [status(thm)], [c_345, c_345, c_2179])).
% 3.92/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.92/1.72  
% 3.92/1.72  Inference rules
% 3.92/1.72  ----------------------
% 3.92/1.72  #Ref     : 0
% 3.92/1.72  #Sup     : 402
% 3.92/1.72  #Fact    : 0
% 3.92/1.72  #Define  : 0
% 3.92/1.72  #Split   : 21
% 3.92/1.72  #Chain   : 0
% 3.92/1.72  #Close   : 0
% 3.92/1.72  
% 3.92/1.72  Ordering : KBO
% 3.92/1.72  
% 3.92/1.72  Simplification rules
% 3.92/1.72  ----------------------
% 3.92/1.72  #Subsume      : 51
% 3.92/1.72  #Demod        : 429
% 3.92/1.72  #Tautology    : 157
% 3.92/1.72  #SimpNegUnit  : 15
% 3.92/1.72  #BackRed      : 74
% 3.92/1.72  
% 3.92/1.72  #Partial instantiations: 0
% 3.92/1.72  #Strategies tried      : 1
% 3.92/1.72  
% 3.92/1.72  Timing (in seconds)
% 3.92/1.72  ----------------------
% 3.92/1.72  Preprocessing        : 0.35
% 3.92/1.72  Parsing              : 0.18
% 3.92/1.72  CNF conversion       : 0.03
% 3.92/1.72  Main loop            : 0.60
% 3.92/1.72  Inferencing          : 0.20
% 3.92/1.72  Reduction            : 0.20
% 3.92/1.72  Demodulation         : 0.14
% 3.92/1.72  BG Simplification    : 0.03
% 3.92/1.72  Subsumption          : 0.12
% 3.92/1.72  Abstraction          : 0.03
% 3.92/1.72  MUC search           : 0.00
% 3.92/1.72  Cooper               : 0.00
% 3.92/1.72  Total                : 0.97
% 3.92/1.72  Index Insertion      : 0.00
% 3.92/1.72  Index Deletion       : 0.00
% 3.92/1.72  Index Matching       : 0.00
% 3.92/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
