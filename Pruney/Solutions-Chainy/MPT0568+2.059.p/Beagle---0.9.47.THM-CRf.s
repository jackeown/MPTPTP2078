%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:28 EST 2020

% Result     : Theorem 8.06s
% Output     : CNFRefutation 8.48s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 199 expanded)
%              Number of leaves         :   41 (  83 expanded)
%              Depth                    :   12
%              Number of atoms          :   80 ( 297 expanded)
%              Number of equality atoms :   34 (  80 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_113,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_97,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_121,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_124,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_117,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_127,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_60,plain,(
    ! [A_50] :
      ( r2_hidden('#skF_3'(A_50),A_50)
      | v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_52,plain,(
    ! [A_46] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_46)) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_11748,plain,(
    ! [A_4926,C_4927,B_4928] :
      ( m1_subset_1(A_4926,C_4927)
      | ~ m1_subset_1(B_4928,k1_zfmisc_1(C_4927))
      | ~ r2_hidden(A_4926,B_4928) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_11757,plain,(
    ! [A_4979,A_4980] :
      ( m1_subset_1(A_4979,A_4980)
      | ~ r2_hidden(A_4979,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_52,c_11748])).

tff(c_11766,plain,(
    ! [A_4980] :
      ( m1_subset_1('#skF_3'(k1_xboole_0),A_4980)
      | v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_60,c_11757])).

tff(c_11767,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_11766])).

tff(c_64,plain,(
    ! [A_70] :
      ( k10_relat_1(A_70,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_11807,plain,(
    k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_11767,c_64])).

tff(c_173,plain,(
    ! [A_97,B_98] : k4_xboole_0(A_97,k4_xboole_0(A_97,B_98)) = k3_xboole_0(A_97,B_98) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_16] : k4_xboole_0(k1_xboole_0,A_16) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_183,plain,(
    ! [B_98] : k3_xboole_0(k1_xboole_0,B_98) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_14])).

tff(c_66,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_13690,plain,(
    ! [B_5359,A_5360] :
      ( k10_relat_1(B_5359,k3_xboole_0(k2_relat_1(B_5359),A_5360)) = k10_relat_1(B_5359,A_5360)
      | ~ v1_relat_1(B_5359) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_13715,plain,(
    ! [A_5360] :
      ( k10_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,A_5360)) = k10_relat_1(k1_xboole_0,A_5360)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_13690])).

tff(c_13720,plain,(
    ! [A_5360] : k10_relat_1(k1_xboole_0,A_5360) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_11767,c_11807,c_183,c_13715])).

tff(c_70,plain,(
    k10_relat_1(k1_xboole_0,'#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_13724,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13720,c_70])).

tff(c_13726,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_11766])).

tff(c_46,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(k1_tarski(A_37),B_38)
      | ~ r2_hidden(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_14223,plain,(
    ! [A_5616,B_5617,C_5618] : k4_xboole_0(k3_xboole_0(A_5616,B_5617),C_5618) = k3_xboole_0(A_5616,k4_xboole_0(B_5617,C_5618)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_107,plain,(
    ! [A_78,B_79] : k4_xboole_0(A_78,k2_xboole_0(A_78,B_79)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_117,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_107])).

tff(c_14666,plain,(
    ! [A_5669,B_5670] : k3_xboole_0(A_5669,k4_xboole_0(B_5670,k3_xboole_0(A_5669,B_5670))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14223,c_117])).

tff(c_4,plain,(
    ! [A_4,B_5,C_6] :
      ( r1_tarski(A_4,B_5)
      | ~ r1_tarski(A_4,k3_xboole_0(B_5,C_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_15268,plain,(
    ! [A_5723,A_5724] :
      ( r1_tarski(A_5723,A_5724)
      | ~ r1_tarski(A_5723,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14666,c_4])).

tff(c_15274,plain,(
    ! [A_5725,A_5726] :
      ( r1_tarski(k1_tarski(A_5725),A_5726)
      | ~ r2_hidden(A_5725,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_46,c_15268])).

tff(c_44,plain,(
    ! [A_37,B_38] :
      ( r2_hidden(A_37,B_38)
      | ~ r1_tarski(k1_tarski(A_37),B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_15293,plain,(
    ! [A_5727,A_5728] :
      ( r2_hidden(A_5727,A_5728)
      | ~ r2_hidden(A_5727,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_15274,c_44])).

tff(c_15296,plain,(
    ! [A_5728] :
      ( r2_hidden('#skF_3'(k1_xboole_0),A_5728)
      | v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_60,c_15293])).

tff(c_15392,plain,(
    ! [A_5732] : r2_hidden('#skF_3'(k1_xboole_0),A_5732) ),
    inference(negUnitSimplification,[status(thm)],[c_13726,c_15296])).

tff(c_22,plain,(
    ! [C_30,A_26] :
      ( C_30 = A_26
      | ~ r2_hidden(C_30,k1_tarski(A_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_15427,plain,(
    '#skF_3'(k1_xboole_0) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_15392,c_22])).

tff(c_15416,plain,(
    ! [A_26] : A_26 = '#skF_3'(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_15392,c_22])).

tff(c_15428,plain,(
    ! [A_26] : A_26 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_15427,c_15416])).

tff(c_15669,plain,(
    ! [A_6934] : A_6934 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_15427,c_15416])).

tff(c_15820,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_15669,c_70])).

tff(c_15834,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_15428,c_15820])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:14:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.06/2.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.06/2.78  
% 8.06/2.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.06/2.78  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 8.06/2.78  
% 8.06/2.78  %Foreground sorts:
% 8.06/2.78  
% 8.06/2.78  
% 8.06/2.78  %Background operators:
% 8.06/2.78  
% 8.06/2.78  
% 8.06/2.78  %Foreground operators:
% 8.06/2.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.06/2.78  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.06/2.78  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.06/2.78  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.06/2.78  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 8.06/2.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.06/2.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.06/2.78  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.06/2.78  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.06/2.78  tff('#skF_6', type, '#skF_6': $i).
% 8.06/2.78  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.06/2.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.06/2.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.06/2.78  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 8.06/2.78  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.06/2.78  tff('#skF_3', type, '#skF_3': $i > $i).
% 8.06/2.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.06/2.78  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.06/2.78  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.06/2.78  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.06/2.78  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.06/2.78  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.06/2.78  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 8.06/2.78  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.06/2.78  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 8.06/2.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.06/2.78  
% 8.48/2.79  tff(f_113, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 8.48/2.79  tff(f_97, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 8.48/2.79  tff(f_103, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 8.48/2.79  tff(f_121, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_relat_1)).
% 8.48/2.79  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.48/2.79  tff(f_41, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 8.48/2.79  tff(f_124, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 8.48/2.79  tff(f_117, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 8.48/2.79  tff(f_127, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 8.48/2.79  tff(f_78, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_zfmisc_1)).
% 8.48/2.79  tff(f_39, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 8.48/2.79  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 8.48/2.79  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 8.48/2.79  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 8.48/2.79  tff(f_62, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 8.48/2.79  tff(c_60, plain, (![A_50]: (r2_hidden('#skF_3'(A_50), A_50) | v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_113])).
% 8.48/2.79  tff(c_52, plain, (![A_46]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.48/2.79  tff(c_11748, plain, (![A_4926, C_4927, B_4928]: (m1_subset_1(A_4926, C_4927) | ~m1_subset_1(B_4928, k1_zfmisc_1(C_4927)) | ~r2_hidden(A_4926, B_4928))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.48/2.79  tff(c_11757, plain, (![A_4979, A_4980]: (m1_subset_1(A_4979, A_4980) | ~r2_hidden(A_4979, k1_xboole_0))), inference(resolution, [status(thm)], [c_52, c_11748])).
% 8.48/2.79  tff(c_11766, plain, (![A_4980]: (m1_subset_1('#skF_3'(k1_xboole_0), A_4980) | v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_60, c_11757])).
% 8.48/2.79  tff(c_11767, plain, (v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_11766])).
% 8.48/2.79  tff(c_64, plain, (![A_70]: (k10_relat_1(A_70, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.48/2.79  tff(c_11807, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_11767, c_64])).
% 8.48/2.79  tff(c_173, plain, (![A_97, B_98]: (k4_xboole_0(A_97, k4_xboole_0(A_97, B_98))=k3_xboole_0(A_97, B_98))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.48/2.79  tff(c_14, plain, (![A_16]: (k4_xboole_0(k1_xboole_0, A_16)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.48/2.79  tff(c_183, plain, (![B_98]: (k3_xboole_0(k1_xboole_0, B_98)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_173, c_14])).
% 8.48/2.79  tff(c_66, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_124])).
% 8.48/2.79  tff(c_13690, plain, (![B_5359, A_5360]: (k10_relat_1(B_5359, k3_xboole_0(k2_relat_1(B_5359), A_5360))=k10_relat_1(B_5359, A_5360) | ~v1_relat_1(B_5359))), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.48/2.79  tff(c_13715, plain, (![A_5360]: (k10_relat_1(k1_xboole_0, k3_xboole_0(k1_xboole_0, A_5360))=k10_relat_1(k1_xboole_0, A_5360) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_66, c_13690])).
% 8.48/2.79  tff(c_13720, plain, (![A_5360]: (k10_relat_1(k1_xboole_0, A_5360)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_11767, c_11807, c_183, c_13715])).
% 8.48/2.79  tff(c_70, plain, (k10_relat_1(k1_xboole_0, '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.48/2.79  tff(c_13724, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13720, c_70])).
% 8.48/2.79  tff(c_13726, plain, (~v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_11766])).
% 8.48/2.79  tff(c_46, plain, (![A_37, B_38]: (r1_tarski(k1_tarski(A_37), B_38) | ~r2_hidden(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.48/2.79  tff(c_14223, plain, (![A_5616, B_5617, C_5618]: (k4_xboole_0(k3_xboole_0(A_5616, B_5617), C_5618)=k3_xboole_0(A_5616, k4_xboole_0(B_5617, C_5618)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.48/2.79  tff(c_6, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k3_xboole_0(A_7, B_8))=A_7)), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.48/2.79  tff(c_107, plain, (![A_78, B_79]: (k4_xboole_0(A_78, k2_xboole_0(A_78, B_79))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.48/2.79  tff(c_117, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_107])).
% 8.48/2.79  tff(c_14666, plain, (![A_5669, B_5670]: (k3_xboole_0(A_5669, k4_xboole_0(B_5670, k3_xboole_0(A_5669, B_5670)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14223, c_117])).
% 8.48/2.79  tff(c_4, plain, (![A_4, B_5, C_6]: (r1_tarski(A_4, B_5) | ~r1_tarski(A_4, k3_xboole_0(B_5, C_6)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.48/2.79  tff(c_15268, plain, (![A_5723, A_5724]: (r1_tarski(A_5723, A_5724) | ~r1_tarski(A_5723, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14666, c_4])).
% 8.48/2.79  tff(c_15274, plain, (![A_5725, A_5726]: (r1_tarski(k1_tarski(A_5725), A_5726) | ~r2_hidden(A_5725, k1_xboole_0))), inference(resolution, [status(thm)], [c_46, c_15268])).
% 8.48/2.79  tff(c_44, plain, (![A_37, B_38]: (r2_hidden(A_37, B_38) | ~r1_tarski(k1_tarski(A_37), B_38))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.48/2.79  tff(c_15293, plain, (![A_5727, A_5728]: (r2_hidden(A_5727, A_5728) | ~r2_hidden(A_5727, k1_xboole_0))), inference(resolution, [status(thm)], [c_15274, c_44])).
% 8.48/2.79  tff(c_15296, plain, (![A_5728]: (r2_hidden('#skF_3'(k1_xboole_0), A_5728) | v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_60, c_15293])).
% 8.48/2.79  tff(c_15392, plain, (![A_5732]: (r2_hidden('#skF_3'(k1_xboole_0), A_5732))), inference(negUnitSimplification, [status(thm)], [c_13726, c_15296])).
% 8.48/2.79  tff(c_22, plain, (![C_30, A_26]: (C_30=A_26 | ~r2_hidden(C_30, k1_tarski(A_26)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.48/2.79  tff(c_15427, plain, ('#skF_3'(k1_xboole_0)='#skF_6'), inference(resolution, [status(thm)], [c_15392, c_22])).
% 8.48/2.79  tff(c_15416, plain, (![A_26]: (A_26='#skF_3'(k1_xboole_0))), inference(resolution, [status(thm)], [c_15392, c_22])).
% 8.48/2.79  tff(c_15428, plain, (![A_26]: (A_26='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_15427, c_15416])).
% 8.48/2.79  tff(c_15669, plain, (![A_6934]: (A_6934='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_15427, c_15416])).
% 8.48/2.79  tff(c_15820, plain, (k1_xboole_0!='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_15669, c_70])).
% 8.48/2.79  tff(c_15834, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_15428, c_15820])).
% 8.48/2.79  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.48/2.79  
% 8.48/2.79  Inference rules
% 8.48/2.79  ----------------------
% 8.48/2.79  #Ref     : 0
% 8.48/2.79  #Sup     : 2882
% 8.48/2.79  #Fact    : 1
% 8.48/2.79  #Define  : 0
% 8.48/2.79  #Split   : 4
% 8.48/2.79  #Chain   : 0
% 8.48/2.79  #Close   : 0
% 8.48/2.79  
% 8.48/2.79  Ordering : KBO
% 8.48/2.79  
% 8.48/2.79  Simplification rules
% 8.48/2.79  ----------------------
% 8.48/2.79  #Subsume      : 914
% 8.48/2.79  #Demod        : 1233
% 8.48/2.79  #Tautology    : 468
% 8.48/2.79  #SimpNegUnit  : 61
% 8.48/2.79  #BackRed      : 12
% 8.48/2.79  
% 8.48/2.79  #Partial instantiations: 2929
% 8.48/2.79  #Strategies tried      : 1
% 8.48/2.79  
% 8.48/2.79  Timing (in seconds)
% 8.48/2.79  ----------------------
% 8.48/2.80  Preprocessing        : 0.37
% 8.48/2.80  Parsing              : 0.19
% 8.48/2.80  CNF conversion       : 0.03
% 8.48/2.80  Main loop            : 1.65
% 8.48/2.80  Inferencing          : 0.58
% 8.48/2.80  Reduction            : 0.63
% 8.50/2.80  Demodulation         : 0.46
% 8.50/2.80  BG Simplification    : 0.08
% 8.50/2.80  Subsumption          : 0.27
% 8.50/2.80  Abstraction          : 0.12
% 8.50/2.80  MUC search           : 0.00
% 8.50/2.80  Cooper               : 0.00
% 8.50/2.80  Total                : 2.05
% 8.50/2.80  Index Insertion      : 0.00
% 8.50/2.80  Index Deletion       : 0.00
% 8.50/2.80  Index Matching       : 0.00
% 8.50/2.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
