%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:27 EST 2020

% Result     : Theorem 3.64s
% Output     : CNFRefutation 3.64s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 186 expanded)
%              Number of leaves         :   33 (  82 expanded)
%              Depth                    :   10
%              Number of atoms          :  130 ( 625 expanded)
%              Number of equality atoms :   19 (  84 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_132,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ~ ( B != k1_xboole_0
            & ? [D] :
                ( v1_funct_1(D)
                & v1_funct_2(D,B,A)
                & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A)))
                & r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A)) )
            & ~ v2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_funct_2)).

tff(f_87,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_61,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_81,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_109,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | v2_funct_1(D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v1_xboole_0(A)
        & v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(c_42,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_58,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_56,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_54,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_50,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_48,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_36,plain,(
    ! [A_21] : k6_relat_1(A_21) = k6_partfun1(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_22,plain,(
    ! [A_9] : v2_funct_1(k6_relat_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_59,plain,(
    ! [A_9] : v2_funct_1(k6_partfun1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_22])).

tff(c_737,plain,(
    ! [D_162,C_163,A_165,B_164,F_161,E_160] :
      ( m1_subset_1(k1_partfun1(A_165,B_164,C_163,D_162,E_160,F_161),k1_zfmisc_1(k2_zfmisc_1(A_165,D_162)))
      | ~ m1_subset_1(F_161,k1_zfmisc_1(k2_zfmisc_1(C_163,D_162)))
      | ~ v1_funct_1(F_161)
      | ~ m1_subset_1(E_160,k1_zfmisc_1(k2_zfmisc_1(A_165,B_164)))
      | ~ v1_funct_1(E_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_34,plain,(
    ! [A_20] : m1_subset_1(k6_partfun1(A_20),k1_zfmisc_1(k2_zfmisc_1(A_20,A_20))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_44,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_648,plain,(
    ! [D_140,C_141,A_142,B_143] :
      ( D_140 = C_141
      | ~ r2_relset_1(A_142,B_143,C_141,D_140)
      | ~ m1_subset_1(D_140,k1_zfmisc_1(k2_zfmisc_1(A_142,B_143)))
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_142,B_143))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_654,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_44,c_648])).

tff(c_665,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_654])).

tff(c_684,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_665])).

tff(c_745,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_737,c_684])).

tff(c_762,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_50,c_46,c_745])).

tff(c_763,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_665])).

tff(c_960,plain,(
    ! [B_226,E_223,C_224,D_225,A_222] :
      ( k1_xboole_0 = C_224
      | v2_funct_1(D_225)
      | ~ v2_funct_1(k1_partfun1(A_222,B_226,B_226,C_224,D_225,E_223))
      | ~ m1_subset_1(E_223,k1_zfmisc_1(k2_zfmisc_1(B_226,C_224)))
      | ~ v1_funct_2(E_223,B_226,C_224)
      | ~ v1_funct_1(E_223)
      | ~ m1_subset_1(D_225,k1_zfmisc_1(k2_zfmisc_1(A_222,B_226)))
      | ~ v1_funct_2(D_225,A_222,B_226)
      | ~ v1_funct_1(D_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_962,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_763,c_960])).

tff(c_967,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_50,c_48,c_46,c_59,c_962])).

tff(c_968,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_967])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_994,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_968,c_2])).

tff(c_8,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_990,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_1',B_2) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_968,c_968,c_8])).

tff(c_142,plain,(
    ! [A_39] :
      ( v2_funct_1(A_39)
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39)
      | ~ v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_145,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_142,c_42])).

tff(c_148,plain,
    ( ~ v1_relat_1('#skF_3')
    | ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_145])).

tff(c_149,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_148])).

tff(c_115,plain,(
    ! [B_37,A_38] :
      ( v1_xboole_0(B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_38))
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_133,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_54,c_115])).

tff(c_150,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_133])).

tff(c_1065,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_990,c_150])).

tff(c_1069,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_994,c_1065])).

tff(c_1070,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_1071,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_12,plain,(
    ! [A_6] :
      ( v1_relat_1(A_6)
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1077,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1071,c_12])).

tff(c_1083,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1070,c_1077])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:25:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.64/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.64/1.56  
% 3.64/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.64/1.56  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.64/1.56  
% 3.64/1.56  %Foreground sorts:
% 3.64/1.56  
% 3.64/1.56  
% 3.64/1.56  %Background operators:
% 3.64/1.56  
% 3.64/1.56  
% 3.64/1.56  %Foreground operators:
% 3.64/1.56  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.64/1.56  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.64/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.64/1.56  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.64/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.64/1.56  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.64/1.56  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.64/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.64/1.56  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.64/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.64/1.56  tff('#skF_1', type, '#skF_1': $i).
% 3.64/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.64/1.56  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.64/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.64/1.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.64/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.64/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.64/1.56  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.64/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.64/1.56  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.64/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.64/1.56  
% 3.64/1.57  tff(f_132, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~((~(B = k1_xboole_0) & (?[D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))))) & ~v2_funct_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_funct_2)).
% 3.64/1.57  tff(f_87, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.64/1.57  tff(f_61, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 3.64/1.57  tff(f_81, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 3.64/1.57  tff(f_85, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 3.64/1.57  tff(f_69, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.64/1.57  tff(f_109, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 3.64/1.57  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.64/1.57  tff(f_32, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.64/1.57  tff(f_59, axiom, (![A]: (((v1_xboole_0(A) & v1_relat_1(A)) & v1_funct_1(A)) => ((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_1)).
% 3.64/1.57  tff(f_39, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 3.64/1.57  tff(f_43, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 3.64/1.57  tff(c_42, plain, (~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.64/1.57  tff(c_58, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.64/1.57  tff(c_56, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.64/1.57  tff(c_54, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.64/1.57  tff(c_50, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.64/1.57  tff(c_48, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.64/1.57  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.64/1.57  tff(c_36, plain, (![A_21]: (k6_relat_1(A_21)=k6_partfun1(A_21))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.64/1.57  tff(c_22, plain, (![A_9]: (v2_funct_1(k6_relat_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.64/1.57  tff(c_59, plain, (![A_9]: (v2_funct_1(k6_partfun1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_22])).
% 3.64/1.57  tff(c_737, plain, (![D_162, C_163, A_165, B_164, F_161, E_160]: (m1_subset_1(k1_partfun1(A_165, B_164, C_163, D_162, E_160, F_161), k1_zfmisc_1(k2_zfmisc_1(A_165, D_162))) | ~m1_subset_1(F_161, k1_zfmisc_1(k2_zfmisc_1(C_163, D_162))) | ~v1_funct_1(F_161) | ~m1_subset_1(E_160, k1_zfmisc_1(k2_zfmisc_1(A_165, B_164))) | ~v1_funct_1(E_160))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.64/1.57  tff(c_34, plain, (![A_20]: (m1_subset_1(k6_partfun1(A_20), k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.64/1.57  tff(c_44, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.64/1.57  tff(c_648, plain, (![D_140, C_141, A_142, B_143]: (D_140=C_141 | ~r2_relset_1(A_142, B_143, C_141, D_140) | ~m1_subset_1(D_140, k1_zfmisc_1(k2_zfmisc_1(A_142, B_143))) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_142, B_143))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.64/1.57  tff(c_654, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_44, c_648])).
% 3.64/1.57  tff(c_665, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_654])).
% 3.64/1.57  tff(c_684, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_665])).
% 3.64/1.57  tff(c_745, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_737, c_684])).
% 3.64/1.57  tff(c_762, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_50, c_46, c_745])).
% 3.64/1.57  tff(c_763, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_665])).
% 3.64/1.57  tff(c_960, plain, (![B_226, E_223, C_224, D_225, A_222]: (k1_xboole_0=C_224 | v2_funct_1(D_225) | ~v2_funct_1(k1_partfun1(A_222, B_226, B_226, C_224, D_225, E_223)) | ~m1_subset_1(E_223, k1_zfmisc_1(k2_zfmisc_1(B_226, C_224))) | ~v1_funct_2(E_223, B_226, C_224) | ~v1_funct_1(E_223) | ~m1_subset_1(D_225, k1_zfmisc_1(k2_zfmisc_1(A_222, B_226))) | ~v1_funct_2(D_225, A_222, B_226) | ~v1_funct_1(D_225))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.64/1.57  tff(c_962, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_763, c_960])).
% 3.64/1.57  tff(c_967, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_50, c_48, c_46, c_59, c_962])).
% 3.64/1.57  tff(c_968, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_42, c_967])).
% 3.64/1.57  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.64/1.57  tff(c_994, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_968, c_2])).
% 3.64/1.57  tff(c_8, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.64/1.57  tff(c_990, plain, (![B_2]: (k2_zfmisc_1('#skF_1', B_2)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_968, c_968, c_8])).
% 3.64/1.57  tff(c_142, plain, (![A_39]: (v2_funct_1(A_39) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39) | ~v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.64/1.57  tff(c_145, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_142, c_42])).
% 3.64/1.57  tff(c_148, plain, (~v1_relat_1('#skF_3') | ~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_145])).
% 3.64/1.57  tff(c_149, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_148])).
% 3.64/1.57  tff(c_115, plain, (![B_37, A_38]: (v1_xboole_0(B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(A_38)) | ~v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.64/1.57  tff(c_133, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_54, c_115])).
% 3.64/1.57  tff(c_150, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_149, c_133])).
% 3.64/1.57  tff(c_1065, plain, (~v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_990, c_150])).
% 3.64/1.57  tff(c_1069, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_994, c_1065])).
% 3.64/1.57  tff(c_1070, plain, (~v1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_148])).
% 3.64/1.57  tff(c_1071, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_148])).
% 3.64/1.57  tff(c_12, plain, (![A_6]: (v1_relat_1(A_6) | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.64/1.57  tff(c_1077, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1071, c_12])).
% 3.64/1.57  tff(c_1083, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1070, c_1077])).
% 3.64/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.64/1.57  
% 3.64/1.57  Inference rules
% 3.64/1.57  ----------------------
% 3.64/1.57  #Ref     : 0
% 3.64/1.57  #Sup     : 211
% 3.64/1.57  #Fact    : 0
% 3.64/1.57  #Define  : 0
% 3.64/1.57  #Split   : 4
% 3.64/1.57  #Chain   : 0
% 3.64/1.57  #Close   : 0
% 3.64/1.57  
% 3.64/1.57  Ordering : KBO
% 3.64/1.57  
% 3.64/1.57  Simplification rules
% 3.64/1.57  ----------------------
% 3.64/1.57  #Subsume      : 0
% 3.64/1.57  #Demod        : 249
% 3.64/1.57  #Tautology    : 64
% 3.64/1.57  #SimpNegUnit  : 4
% 3.64/1.57  #BackRed      : 61
% 3.64/1.57  
% 3.64/1.57  #Partial instantiations: 0
% 3.64/1.57  #Strategies tried      : 1
% 3.64/1.57  
% 3.64/1.57  Timing (in seconds)
% 3.64/1.57  ----------------------
% 3.64/1.58  Preprocessing        : 0.34
% 3.64/1.58  Parsing              : 0.18
% 3.64/1.58  CNF conversion       : 0.02
% 3.64/1.58  Main loop            : 0.48
% 3.64/1.58  Inferencing          : 0.18
% 3.64/1.58  Reduction            : 0.17
% 3.64/1.58  Demodulation         : 0.12
% 3.64/1.58  BG Simplification    : 0.02
% 3.64/1.58  Subsumption          : 0.08
% 3.64/1.58  Abstraction          : 0.02
% 3.64/1.58  MUC search           : 0.00
% 3.64/1.58  Cooper               : 0.00
% 3.64/1.58  Total                : 0.85
% 3.64/1.58  Index Insertion      : 0.00
% 3.64/1.58  Index Deletion       : 0.00
% 3.64/1.58  Index Matching       : 0.00
% 3.64/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
