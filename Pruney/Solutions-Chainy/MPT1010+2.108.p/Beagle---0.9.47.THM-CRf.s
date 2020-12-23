%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:19 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :   77 (  83 expanded)
%              Number of leaves         :   42 (  47 expanded)
%              Depth                    :   13
%              Number of atoms          :  106 ( 128 expanded)
%              Number of equality atoms :   34 (  38 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_124,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_57,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_28,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_80,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_101,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
        & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( v1_xboole_0(A)
        & v1_relat_1(B) )
     => ( v1_xboole_0(k5_relat_1(B,A))
        & v1_relat_1(k5_relat_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_relat_1)).

tff(f_82,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(f_95,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( A != k1_xboole_0
          & r1_tarski(A,k1_relat_1(B))
          & k9_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
     => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_44,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_113,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_35,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_56,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_30,plain,(
    ! [A_20] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_40,plain,(
    ! [A_29,B_30] : v1_relat_1(k2_zfmisc_1(A_29,B_30)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_85,plain,(
    ! [A_48] :
      ( k5_relat_1(A_48,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_89,plain,(
    ! [A_29,B_30] : k5_relat_1(k2_zfmisc_1(A_29,B_30),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_85])).

tff(c_115,plain,(
    ! [B_56,A_57] :
      ( v1_relat_1(k5_relat_1(B_56,A_57))
      | ~ v1_relat_1(B_56)
      | ~ v1_xboole_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_127,plain,(
    ! [A_29,B_30] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k2_zfmisc_1(A_29,B_30))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_115])).

tff(c_131,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_40,c_127])).

tff(c_42,plain,(
    ! [A_31] : k9_relat_1(k1_xboole_0,A_31) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_48,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_368,plain,(
    ! [B_94,A_95] :
      ( k9_relat_1(B_94,A_95) != k1_xboole_0
      | ~ r1_tarski(A_95,k1_relat_1(B_94))
      | k1_xboole_0 = A_95
      | ~ v1_relat_1(B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_375,plain,(
    ! [A_95] :
      ( k9_relat_1(k1_xboole_0,A_95) != k1_xboole_0
      | ~ r1_tarski(A_95,k1_xboole_0)
      | k1_xboole_0 = A_95
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_368])).

tff(c_379,plain,(
    ! [A_96] :
      ( ~ r1_tarski(A_96,k1_xboole_0)
      | k1_xboole_0 = A_96 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_42,c_375])).

tff(c_385,plain,(
    ! [B_97] : k3_xboole_0(k1_xboole_0,B_97) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_379])).

tff(c_26,plain,(
    ! [B_15,A_14] :
      ( r2_hidden(B_15,A_14)
      | k3_xboole_0(A_14,k1_tarski(B_15)) != k1_tarski(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_421,plain,(
    ! [B_102] :
      ( r2_hidden(B_102,k1_xboole_0)
      | k1_tarski(B_102) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_385,c_26])).

tff(c_28,plain,(
    ! [C_19,A_16,B_17] :
      ( r2_hidden(C_19,A_16)
      | ~ r2_hidden(C_19,B_17)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_427,plain,(
    ! [B_102,A_16] :
      ( r2_hidden(B_102,A_16)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_16))
      | k1_tarski(B_102) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_421,c_28])).

tff(c_435,plain,(
    ! [B_103,A_104] :
      ( r2_hidden(B_103,A_104)
      | k1_tarski(B_103) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_427])).

tff(c_24,plain,(
    ! [A_12,B_13] : ~ r2_hidden(A_12,k2_zfmisc_1(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_464,plain,(
    ! [B_103] : k1_tarski(B_103) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_435,c_24])).

tff(c_64,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_62,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_60,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_58,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_495,plain,(
    ! [D_111,C_112,B_113,A_114] :
      ( r2_hidden(k1_funct_1(D_111,C_112),B_113)
      | k1_xboole_0 = B_113
      | ~ r2_hidden(C_112,A_114)
      | ~ m1_subset_1(D_111,k1_zfmisc_1(k2_zfmisc_1(A_114,B_113)))
      | ~ v1_funct_2(D_111,A_114,B_113)
      | ~ v1_funct_1(D_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_512,plain,(
    ! [D_117,B_118] :
      ( r2_hidden(k1_funct_1(D_117,'#skF_5'),B_118)
      | k1_xboole_0 = B_118
      | ~ m1_subset_1(D_117,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_118)))
      | ~ v1_funct_2(D_117,'#skF_3',B_118)
      | ~ v1_funct_1(D_117) ) ),
    inference(resolution,[status(thm)],[c_58,c_495])).

tff(c_515,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_512])).

tff(c_522,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_515])).

tff(c_523,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_464,c_522])).

tff(c_6,plain,(
    ! [C_7,A_3] :
      ( C_7 = A_3
      | ~ r2_hidden(C_7,k1_tarski(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_531,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_523,c_6])).

tff(c_537,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_531])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:38:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.50/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.41  
% 2.50/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.41  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.50/1.41  
% 2.50/1.41  %Foreground sorts:
% 2.50/1.41  
% 2.50/1.41  
% 2.50/1.41  %Background operators:
% 2.50/1.41  
% 2.50/1.41  
% 2.50/1.41  %Foreground operators:
% 2.50/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.50/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.50/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.50/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.50/1.41  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.50/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.50/1.41  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.50/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.50/1.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.50/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.50/1.41  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.50/1.41  tff('#skF_6', type, '#skF_6': $i).
% 2.50/1.41  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.50/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.50/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.50/1.41  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.50/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.50/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.50/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.50/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.50/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.50/1.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.50/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.50/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.50/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.50/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.50/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.50/1.41  
% 2.50/1.43  tff(f_124, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 2.50/1.43  tff(f_57, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.50/1.43  tff(f_28, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.50/1.43  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.50/1.43  tff(f_80, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.50/1.43  tff(f_101, axiom, (![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 2.50/1.43  tff(f_78, axiom, (![A, B]: ((v1_xboole_0(A) & v1_relat_1(B)) => (v1_xboole_0(k5_relat_1(B, A)) & v1_relat_1(k5_relat_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc13_relat_1)).
% 2.50/1.43  tff(f_82, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 2.50/1.43  tff(f_95, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.50/1.43  tff(f_92, axiom, (![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k1_relat_1(B))) & (k9_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_relat_1)).
% 2.50/1.43  tff(f_48, axiom, (![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_zfmisc_1)).
% 2.50/1.43  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 2.50/1.43  tff(f_44, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.50/1.43  tff(f_113, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 2.50/1.43  tff(f_35, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.50/1.43  tff(c_56, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.50/1.43  tff(c_30, plain, (![A_20]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.50/1.43  tff(c_4, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.50/1.43  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.50/1.43  tff(c_40, plain, (![A_29, B_30]: (v1_relat_1(k2_zfmisc_1(A_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.50/1.43  tff(c_85, plain, (![A_48]: (k5_relat_1(A_48, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.50/1.43  tff(c_89, plain, (![A_29, B_30]: (k5_relat_1(k2_zfmisc_1(A_29, B_30), k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_85])).
% 2.50/1.43  tff(c_115, plain, (![B_56, A_57]: (v1_relat_1(k5_relat_1(B_56, A_57)) | ~v1_relat_1(B_56) | ~v1_xboole_0(A_57))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.50/1.43  tff(c_127, plain, (![A_29, B_30]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(k2_zfmisc_1(A_29, B_30)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_89, c_115])).
% 2.50/1.43  tff(c_131, plain, (v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_40, c_127])).
% 2.50/1.43  tff(c_42, plain, (![A_31]: (k9_relat_1(k1_xboole_0, A_31)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.50/1.43  tff(c_48, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.50/1.43  tff(c_368, plain, (![B_94, A_95]: (k9_relat_1(B_94, A_95)!=k1_xboole_0 | ~r1_tarski(A_95, k1_relat_1(B_94)) | k1_xboole_0=A_95 | ~v1_relat_1(B_94))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.50/1.43  tff(c_375, plain, (![A_95]: (k9_relat_1(k1_xboole_0, A_95)!=k1_xboole_0 | ~r1_tarski(A_95, k1_xboole_0) | k1_xboole_0=A_95 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_48, c_368])).
% 2.50/1.43  tff(c_379, plain, (![A_96]: (~r1_tarski(A_96, k1_xboole_0) | k1_xboole_0=A_96)), inference(demodulation, [status(thm), theory('equality')], [c_131, c_42, c_375])).
% 2.50/1.43  tff(c_385, plain, (![B_97]: (k3_xboole_0(k1_xboole_0, B_97)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_379])).
% 2.50/1.43  tff(c_26, plain, (![B_15, A_14]: (r2_hidden(B_15, A_14) | k3_xboole_0(A_14, k1_tarski(B_15))!=k1_tarski(B_15))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.50/1.43  tff(c_421, plain, (![B_102]: (r2_hidden(B_102, k1_xboole_0) | k1_tarski(B_102)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_385, c_26])).
% 2.50/1.43  tff(c_28, plain, (![C_19, A_16, B_17]: (r2_hidden(C_19, A_16) | ~r2_hidden(C_19, B_17) | ~m1_subset_1(B_17, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.50/1.43  tff(c_427, plain, (![B_102, A_16]: (r2_hidden(B_102, A_16) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_16)) | k1_tarski(B_102)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_421, c_28])).
% 2.50/1.43  tff(c_435, plain, (![B_103, A_104]: (r2_hidden(B_103, A_104) | k1_tarski(B_103)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_427])).
% 2.50/1.43  tff(c_24, plain, (![A_12, B_13]: (~r2_hidden(A_12, k2_zfmisc_1(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.50/1.43  tff(c_464, plain, (![B_103]: (k1_tarski(B_103)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_435, c_24])).
% 2.50/1.43  tff(c_64, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.50/1.43  tff(c_62, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.50/1.43  tff(c_60, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.50/1.43  tff(c_58, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.50/1.43  tff(c_495, plain, (![D_111, C_112, B_113, A_114]: (r2_hidden(k1_funct_1(D_111, C_112), B_113) | k1_xboole_0=B_113 | ~r2_hidden(C_112, A_114) | ~m1_subset_1(D_111, k1_zfmisc_1(k2_zfmisc_1(A_114, B_113))) | ~v1_funct_2(D_111, A_114, B_113) | ~v1_funct_1(D_111))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.50/1.43  tff(c_512, plain, (![D_117, B_118]: (r2_hidden(k1_funct_1(D_117, '#skF_5'), B_118) | k1_xboole_0=B_118 | ~m1_subset_1(D_117, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_118))) | ~v1_funct_2(D_117, '#skF_3', B_118) | ~v1_funct_1(D_117))), inference(resolution, [status(thm)], [c_58, c_495])).
% 2.50/1.43  tff(c_515, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_60, c_512])).
% 2.50/1.43  tff(c_522, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_515])).
% 2.50/1.43  tff(c_523, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_464, c_522])).
% 2.50/1.43  tff(c_6, plain, (![C_7, A_3]: (C_7=A_3 | ~r2_hidden(C_7, k1_tarski(A_3)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.50/1.43  tff(c_531, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_523, c_6])).
% 2.50/1.43  tff(c_537, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_531])).
% 2.50/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.43  
% 2.50/1.43  Inference rules
% 2.50/1.43  ----------------------
% 2.50/1.43  #Ref     : 0
% 2.50/1.43  #Sup     : 108
% 2.50/1.43  #Fact    : 0
% 2.50/1.43  #Define  : 0
% 2.50/1.43  #Split   : 0
% 2.50/1.43  #Chain   : 0
% 2.50/1.43  #Close   : 0
% 2.50/1.43  
% 2.50/1.43  Ordering : KBO
% 2.50/1.43  
% 2.50/1.43  Simplification rules
% 2.50/1.43  ----------------------
% 2.50/1.43  #Subsume      : 9
% 2.50/1.43  #Demod        : 77
% 2.50/1.43  #Tautology    : 57
% 2.50/1.43  #SimpNegUnit  : 2
% 2.50/1.43  #BackRed      : 0
% 2.50/1.43  
% 2.50/1.43  #Partial instantiations: 0
% 2.50/1.43  #Strategies tried      : 1
% 2.50/1.43  
% 2.50/1.43  Timing (in seconds)
% 2.50/1.43  ----------------------
% 2.50/1.43  Preprocessing        : 0.30
% 2.50/1.43  Parsing              : 0.17
% 2.50/1.43  CNF conversion       : 0.02
% 2.50/1.43  Main loop            : 0.28
% 2.50/1.43  Inferencing          : 0.10
% 2.50/1.43  Reduction            : 0.09
% 2.50/1.43  Demodulation         : 0.06
% 2.50/1.43  BG Simplification    : 0.02
% 2.50/1.43  Subsumption          : 0.05
% 2.50/1.43  Abstraction          : 0.01
% 2.50/1.43  MUC search           : 0.00
% 2.50/1.43  Cooper               : 0.00
% 2.50/1.43  Total                : 0.62
% 2.50/1.43  Index Insertion      : 0.00
% 2.50/1.43  Index Deletion       : 0.00
% 2.50/1.43  Index Matching       : 0.00
% 2.50/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
