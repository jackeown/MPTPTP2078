%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:30 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 118 expanded)
%              Number of leaves         :   35 (  57 expanded)
%              Depth                    :   10
%              Number of atoms          :  106 ( 258 expanded)
%              Number of equality atoms :   29 (  63 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_103,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ~ ( r2_hidden(C,k2_relset_1(A,B,D))
            & ! [E] :
                ~ ( r2_hidden(E,A)
                  & k1_funct_1(D,E) = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_funct_2)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_50,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_87,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(c_50,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_67,plain,(
    ! [C_69,B_70,A_71] :
      ( v1_xboole_0(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(B_70,A_71)))
      | ~ v1_xboole_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_71,plain,
    ( v1_xboole_0('#skF_8')
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_67])).

tff(c_72,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_71])).

tff(c_62,plain,(
    ! [C_66,A_67,B_68] :
      ( v1_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_66,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_50,c_62])).

tff(c_54,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_10,plain,(
    ! [A_4,C_40] :
      ( k1_funct_1(A_4,'#skF_4'(A_4,k2_relat_1(A_4),C_40)) = C_40
      | ~ r2_hidden(C_40,k2_relat_1(A_4))
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_52,plain,(
    v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_73,plain,(
    ! [A_72,B_73,C_74] :
      ( k1_relset_1(A_72,B_73,C_74) = k1_relat_1(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_77,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_50,c_73])).

tff(c_169,plain,(
    ! [B_100,A_101,C_102] :
      ( k1_xboole_0 = B_100
      | k1_relset_1(A_101,B_100,C_102) = A_101
      | ~ v1_funct_2(C_102,A_101,B_100)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_101,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_172,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_169])).

tff(c_175,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_77,c_172])).

tff(c_201,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_175])).

tff(c_12,plain,(
    ! [A_4,C_40] :
      ( r2_hidden('#skF_4'(A_4,k2_relat_1(A_4),C_40),k1_relat_1(A_4))
      | ~ r2_hidden(C_40,k2_relat_1(A_4))
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_210,plain,(
    ! [C_40] :
      ( r2_hidden('#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_40),'#skF_5')
      | ~ r2_hidden(C_40,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_12])).

tff(c_228,plain,(
    ! [C_106] :
      ( r2_hidden('#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_106),'#skF_5')
      | ~ r2_hidden(C_106,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_54,c_210])).

tff(c_46,plain,(
    ! [E_61] :
      ( k1_funct_1('#skF_8',E_61) != '#skF_7'
      | ~ r2_hidden(E_61,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_237,plain,(
    ! [C_107] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_107)) != '#skF_7'
      | ~ r2_hidden(C_107,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_228,c_46])).

tff(c_241,plain,(
    ! [C_40] :
      ( C_40 != '#skF_7'
      | ~ r2_hidden(C_40,k2_relat_1('#skF_8'))
      | ~ r2_hidden(C_40,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_237])).

tff(c_244,plain,(
    ~ r2_hidden('#skF_7',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_54,c_241])).

tff(c_83,plain,(
    ! [A_76,B_77,C_78] :
      ( k2_relset_1(A_76,B_77,C_78) = k2_relat_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_87,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_50,c_83])).

tff(c_48,plain,(
    r2_hidden('#skF_7',k2_relset_1('#skF_5','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_89,plain,(
    r2_hidden('#skF_7',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_48])).

tff(c_246,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_244,c_89])).

tff(c_247,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_175])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_255,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_2])).

tff(c_257,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_255])).

tff(c_258,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(k2_relat_1(A_3))
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_260,plain,(
    ! [A_108,B_109,C_110] :
      ( k2_relset_1(A_108,B_109,C_110) = k2_relat_1(C_110)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_264,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_50,c_260])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_60,plain,(
    ~ v1_xboole_0(k2_relset_1('#skF_5','#skF_6','#skF_8')) ),
    inference(resolution,[status(thm)],[c_48,c_4])).

tff(c_265,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_60])).

tff(c_277,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_6,c_265])).

tff(c_281,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_277])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:00:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/1.34  
% 2.44/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/1.35  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1
% 2.44/1.35  
% 2.44/1.35  %Foreground sorts:
% 2.44/1.35  
% 2.44/1.35  
% 2.44/1.35  %Background operators:
% 2.44/1.35  
% 2.44/1.35  
% 2.44/1.35  %Foreground operators:
% 2.44/1.35  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.44/1.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.44/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.44/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.44/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.44/1.35  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.44/1.35  tff('#skF_7', type, '#skF_7': $i).
% 2.44/1.35  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.44/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.44/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.44/1.35  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.44/1.35  tff('#skF_6', type, '#skF_6': $i).
% 2.44/1.35  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.44/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.44/1.35  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.44/1.35  tff('#skF_8', type, '#skF_8': $i).
% 2.44/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.44/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.44/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.44/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.44/1.35  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.44/1.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.44/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.44/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.44/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.44/1.35  
% 2.44/1.36  tff(f_103, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~(r2_hidden(C, k2_relset_1(A, B, D)) & (![E]: ~(r2_hidden(E, A) & (k1_funct_1(D, E) = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_funct_2)).
% 2.44/1.36  tff(f_61, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 2.44/1.36  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.44/1.36  tff(f_50, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 2.44/1.36  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.44/1.36  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.44/1.36  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.44/1.36  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.44/1.36  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc11_relat_1)).
% 2.44/1.36  tff(f_31, axiom, (![A, B]: ~(r2_hidden(A, B) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_boole)).
% 2.44/1.36  tff(c_50, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.44/1.36  tff(c_67, plain, (![C_69, B_70, A_71]: (v1_xboole_0(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(B_70, A_71))) | ~v1_xboole_0(A_71))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.44/1.36  tff(c_71, plain, (v1_xboole_0('#skF_8') | ~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_50, c_67])).
% 2.44/1.36  tff(c_72, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_71])).
% 2.44/1.36  tff(c_62, plain, (![C_66, A_67, B_68]: (v1_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.44/1.36  tff(c_66, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_50, c_62])).
% 2.44/1.36  tff(c_54, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.44/1.36  tff(c_10, plain, (![A_4, C_40]: (k1_funct_1(A_4, '#skF_4'(A_4, k2_relat_1(A_4), C_40))=C_40 | ~r2_hidden(C_40, k2_relat_1(A_4)) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.44/1.36  tff(c_52, plain, (v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.44/1.36  tff(c_73, plain, (![A_72, B_73, C_74]: (k1_relset_1(A_72, B_73, C_74)=k1_relat_1(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.44/1.36  tff(c_77, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_50, c_73])).
% 2.44/1.36  tff(c_169, plain, (![B_100, A_101, C_102]: (k1_xboole_0=B_100 | k1_relset_1(A_101, B_100, C_102)=A_101 | ~v1_funct_2(C_102, A_101, B_100) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_101, B_100))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.44/1.36  tff(c_172, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_50, c_169])).
% 2.44/1.36  tff(c_175, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_77, c_172])).
% 2.44/1.36  tff(c_201, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(splitLeft, [status(thm)], [c_175])).
% 2.44/1.36  tff(c_12, plain, (![A_4, C_40]: (r2_hidden('#skF_4'(A_4, k2_relat_1(A_4), C_40), k1_relat_1(A_4)) | ~r2_hidden(C_40, k2_relat_1(A_4)) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.44/1.36  tff(c_210, plain, (![C_40]: (r2_hidden('#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_40), '#skF_5') | ~r2_hidden(C_40, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_201, c_12])).
% 2.44/1.36  tff(c_228, plain, (![C_106]: (r2_hidden('#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_106), '#skF_5') | ~r2_hidden(C_106, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_54, c_210])).
% 2.44/1.36  tff(c_46, plain, (![E_61]: (k1_funct_1('#skF_8', E_61)!='#skF_7' | ~r2_hidden(E_61, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.44/1.36  tff(c_237, plain, (![C_107]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_107))!='#skF_7' | ~r2_hidden(C_107, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_228, c_46])).
% 2.44/1.36  tff(c_241, plain, (![C_40]: (C_40!='#skF_7' | ~r2_hidden(C_40, k2_relat_1('#skF_8')) | ~r2_hidden(C_40, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_10, c_237])).
% 2.44/1.36  tff(c_244, plain, (~r2_hidden('#skF_7', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_54, c_241])).
% 2.44/1.36  tff(c_83, plain, (![A_76, B_77, C_78]: (k2_relset_1(A_76, B_77, C_78)=k2_relat_1(C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.44/1.36  tff(c_87, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_50, c_83])).
% 2.44/1.36  tff(c_48, plain, (r2_hidden('#skF_7', k2_relset_1('#skF_5', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.44/1.36  tff(c_89, plain, (r2_hidden('#skF_7', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_48])).
% 2.44/1.36  tff(c_246, plain, $false, inference(negUnitSimplification, [status(thm)], [c_244, c_89])).
% 2.44/1.36  tff(c_247, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_175])).
% 2.44/1.36  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.44/1.36  tff(c_255, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_247, c_2])).
% 2.44/1.36  tff(c_257, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_255])).
% 2.44/1.36  tff(c_258, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_71])).
% 2.44/1.36  tff(c_6, plain, (![A_3]: (v1_xboole_0(k2_relat_1(A_3)) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.44/1.36  tff(c_260, plain, (![A_108, B_109, C_110]: (k2_relset_1(A_108, B_109, C_110)=k2_relat_1(C_110) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.44/1.36  tff(c_264, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_50, c_260])).
% 2.44/1.36  tff(c_4, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.44/1.36  tff(c_60, plain, (~v1_xboole_0(k2_relset_1('#skF_5', '#skF_6', '#skF_8'))), inference(resolution, [status(thm)], [c_48, c_4])).
% 2.44/1.36  tff(c_265, plain, (~v1_xboole_0(k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_264, c_60])).
% 2.44/1.36  tff(c_277, plain, (~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_6, c_265])).
% 2.44/1.36  tff(c_281, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_258, c_277])).
% 2.44/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/1.36  
% 2.44/1.36  Inference rules
% 2.44/1.36  ----------------------
% 2.44/1.36  #Ref     : 0
% 2.44/1.36  #Sup     : 45
% 2.44/1.36  #Fact    : 0
% 2.44/1.36  #Define  : 0
% 2.44/1.36  #Split   : 2
% 2.44/1.36  #Chain   : 0
% 2.44/1.36  #Close   : 0
% 2.44/1.36  
% 2.44/1.36  Ordering : KBO
% 2.44/1.36  
% 2.44/1.36  Simplification rules
% 2.44/1.36  ----------------------
% 2.44/1.36  #Subsume      : 8
% 2.44/1.36  #Demod        : 41
% 2.44/1.36  #Tautology    : 14
% 2.44/1.36  #SimpNegUnit  : 2
% 2.44/1.36  #BackRed      : 14
% 2.44/1.36  
% 2.44/1.36  #Partial instantiations: 0
% 2.44/1.36  #Strategies tried      : 1
% 2.44/1.36  
% 2.44/1.36  Timing (in seconds)
% 2.44/1.36  ----------------------
% 2.44/1.37  Preprocessing        : 0.33
% 2.44/1.37  Parsing              : 0.18
% 2.44/1.37  CNF conversion       : 0.03
% 2.44/1.37  Main loop            : 0.21
% 2.44/1.37  Inferencing          : 0.07
% 2.44/1.37  Reduction            : 0.06
% 2.44/1.37  Demodulation         : 0.04
% 2.44/1.37  BG Simplification    : 0.02
% 2.44/1.37  Subsumption          : 0.04
% 2.44/1.37  Abstraction          : 0.01
% 2.44/1.37  MUC search           : 0.00
% 2.44/1.37  Cooper               : 0.00
% 2.44/1.37  Total                : 0.57
% 2.44/1.37  Index Insertion      : 0.00
% 2.44/1.37  Index Deletion       : 0.00
% 2.44/1.37  Index Matching       : 0.00
% 2.44/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
