%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:36 EST 2020

% Result     : Theorem 3.27s
% Output     : CNFRefutation 3.27s
% Verified   : 
% Statistics : Number of formulae       :   71 (  99 expanded)
%              Number of leaves         :   32 (  46 expanded)
%              Depth                    :   13
%              Number of atoms          :   87 ( 142 expanded)
%              Number of equality atoms :   20 (  22 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( r1_tarski(B,C)
         => r2_relset_1(B,A,k5_relset_1(B,A,D,C),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relset_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(c_12,plain,(
    ! [A_13,B_14] : v1_relat_1(k2_zfmisc_1(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_335,plain,(
    ! [B_57,A_58] :
      ( v1_relat_1(B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_58))
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_338,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_32,c_335])).

tff(c_341,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_338])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_30,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_84,plain,(
    ! [A_40,B_41] :
      ( k2_xboole_0(A_40,B_41) = B_41
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_96,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_30,c_84])).

tff(c_113,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_96])).

tff(c_429,plain,(
    ! [C_65,A_66,B_67] :
      ( v4_relat_1(C_65,A_66)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_433,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_429])).

tff(c_987,plain,(
    ! [B_87,A_88] :
      ( k7_relat_1(B_87,A_88) = B_87
      | ~ v4_relat_1(B_87,A_88)
      | ~ v1_relat_1(B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_990,plain,
    ( k7_relat_1('#skF_4','#skF_2') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_433,c_987])).

tff(c_993,plain,(
    k7_relat_1('#skF_4','#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_341,c_990])).

tff(c_16,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_18,A_17)),A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_997,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_993,c_16])).

tff(c_1001,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_341,c_997])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1006,plain,(
    k2_xboole_0(k1_relat_1('#skF_4'),'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1001,c_6])).

tff(c_35,plain,(
    ! [B_36,A_37] : k2_xboole_0(B_36,A_37) = k2_xboole_0(A_37,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_50,plain,(
    ! [A_37,B_36] : r1_tarski(A_37,k2_xboole_0(B_36,A_37)) ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_8])).

tff(c_139,plain,(
    ! [A_42,C_43,B_44] :
      ( r1_tarski(A_42,C_43)
      | ~ r1_tarski(k2_xboole_0(A_42,B_44),C_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_160,plain,(
    ! [A_42,B_36,B_44] : r1_tarski(A_42,k2_xboole_0(B_36,k2_xboole_0(A_42,B_44))) ),
    inference(resolution,[status(thm)],[c_50,c_139])).

tff(c_1329,plain,(
    ! [B_92] : r1_tarski(k1_relat_1('#skF_4'),k2_xboole_0(B_92,'#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1006,c_160])).

tff(c_1341,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_1329])).

tff(c_18,plain,(
    ! [B_20,A_19] :
      ( k7_relat_1(B_20,A_19) = B_20
      | ~ r1_tarski(k1_relat_1(B_20),A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1358,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1341,c_18])).

tff(c_1364,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_341,c_1358])).

tff(c_1516,plain,(
    ! [A_93,B_94,C_95,D_96] :
      ( k5_relset_1(A_93,B_94,C_95,D_96) = k7_relat_1(C_95,D_96)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1519,plain,(
    ! [D_96] : k5_relset_1('#skF_2','#skF_1','#skF_4',D_96) = k7_relat_1('#skF_4',D_96) ),
    inference(resolution,[status(thm)],[c_32,c_1516])).

tff(c_28,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k5_relset_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1563,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1519,c_28])).

tff(c_1564,plain,(
    ~ r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1364,c_1563])).

tff(c_1638,plain,(
    ! [A_101,B_102,C_103,D_104] :
      ( r2_relset_1(A_101,B_102,C_103,C_103)
      | ~ m1_subset_1(D_104,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102)))
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1694,plain,(
    ! [C_106] :
      ( r2_relset_1('#skF_2','#skF_1',C_106,C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_32,c_1638])).

tff(c_1696,plain,(
    r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_1694])).

tff(c_1700,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1564,c_1696])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:53:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.27/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.27/1.50  
% 3.27/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.27/1.51  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.27/1.51  
% 3.27/1.51  %Foreground sorts:
% 3.27/1.51  
% 3.27/1.51  
% 3.27/1.51  %Background operators:
% 3.27/1.51  
% 3.27/1.51  
% 3.27/1.51  %Foreground operators:
% 3.27/1.51  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 3.27/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.27/1.51  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.27/1.51  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.27/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.27/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.27/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.27/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.27/1.51  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.27/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.27/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.27/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.27/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.27/1.51  tff('#skF_4', type, '#skF_4': $i).
% 3.27/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.27/1.51  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.27/1.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.27/1.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.27/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.27/1.51  
% 3.27/1.52  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.27/1.52  tff(f_85, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(B, C) => r2_relset_1(B, A, k5_relset_1(B, A, D, C), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_relset_1)).
% 3.27/1.52  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.27/1.52  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.27/1.52  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.27/1.52  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.27/1.52  tff(f_52, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.27/1.52  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 3.27/1.52  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.27/1.52  tff(f_31, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 3.27/1.52  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 3.27/1.52  tff(f_72, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 3.27/1.52  tff(f_78, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 3.27/1.52  tff(c_12, plain, (![A_13, B_14]: (v1_relat_1(k2_zfmisc_1(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.27/1.52  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.27/1.52  tff(c_335, plain, (![B_57, A_58]: (v1_relat_1(B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(A_58)) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.27/1.52  tff(c_338, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_32, c_335])).
% 3.27/1.52  tff(c_341, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_338])).
% 3.27/1.52  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.27/1.52  tff(c_30, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.27/1.52  tff(c_84, plain, (![A_40, B_41]: (k2_xboole_0(A_40, B_41)=B_41 | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.27/1.52  tff(c_96, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_30, c_84])).
% 3.27/1.52  tff(c_113, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_2, c_96])).
% 3.27/1.52  tff(c_429, plain, (![C_65, A_66, B_67]: (v4_relat_1(C_65, A_66) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.27/1.52  tff(c_433, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_429])).
% 3.27/1.52  tff(c_987, plain, (![B_87, A_88]: (k7_relat_1(B_87, A_88)=B_87 | ~v4_relat_1(B_87, A_88) | ~v1_relat_1(B_87))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.27/1.52  tff(c_990, plain, (k7_relat_1('#skF_4', '#skF_2')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_433, c_987])).
% 3.27/1.52  tff(c_993, plain, (k7_relat_1('#skF_4', '#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_341, c_990])).
% 3.27/1.52  tff(c_16, plain, (![B_18, A_17]: (r1_tarski(k1_relat_1(k7_relat_1(B_18, A_17)), A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.27/1.52  tff(c_997, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_993, c_16])).
% 3.27/1.52  tff(c_1001, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_341, c_997])).
% 3.27/1.52  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.27/1.52  tff(c_1006, plain, (k2_xboole_0(k1_relat_1('#skF_4'), '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_1001, c_6])).
% 3.27/1.52  tff(c_35, plain, (![B_36, A_37]: (k2_xboole_0(B_36, A_37)=k2_xboole_0(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.27/1.52  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.27/1.52  tff(c_50, plain, (![A_37, B_36]: (r1_tarski(A_37, k2_xboole_0(B_36, A_37)))), inference(superposition, [status(thm), theory('equality')], [c_35, c_8])).
% 3.27/1.52  tff(c_139, plain, (![A_42, C_43, B_44]: (r1_tarski(A_42, C_43) | ~r1_tarski(k2_xboole_0(A_42, B_44), C_43))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.27/1.52  tff(c_160, plain, (![A_42, B_36, B_44]: (r1_tarski(A_42, k2_xboole_0(B_36, k2_xboole_0(A_42, B_44))))), inference(resolution, [status(thm)], [c_50, c_139])).
% 3.27/1.52  tff(c_1329, plain, (![B_92]: (r1_tarski(k1_relat_1('#skF_4'), k2_xboole_0(B_92, '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_1006, c_160])).
% 3.27/1.52  tff(c_1341, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_113, c_1329])).
% 3.27/1.52  tff(c_18, plain, (![B_20, A_19]: (k7_relat_1(B_20, A_19)=B_20 | ~r1_tarski(k1_relat_1(B_20), A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.27/1.52  tff(c_1358, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1341, c_18])).
% 3.27/1.52  tff(c_1364, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_341, c_1358])).
% 3.27/1.52  tff(c_1516, plain, (![A_93, B_94, C_95, D_96]: (k5_relset_1(A_93, B_94, C_95, D_96)=k7_relat_1(C_95, D_96) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.27/1.52  tff(c_1519, plain, (![D_96]: (k5_relset_1('#skF_2', '#skF_1', '#skF_4', D_96)=k7_relat_1('#skF_4', D_96))), inference(resolution, [status(thm)], [c_32, c_1516])).
% 3.27/1.52  tff(c_28, plain, (~r2_relset_1('#skF_2', '#skF_1', k5_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.27/1.52  tff(c_1563, plain, (~r2_relset_1('#skF_2', '#skF_1', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1519, c_28])).
% 3.27/1.52  tff(c_1564, plain, (~r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1364, c_1563])).
% 3.27/1.52  tff(c_1638, plain, (![A_101, B_102, C_103, D_104]: (r2_relset_1(A_101, B_102, C_103, C_103) | ~m1_subset_1(D_104, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.27/1.52  tff(c_1694, plain, (![C_106]: (r2_relset_1('#skF_2', '#skF_1', C_106, C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))))), inference(resolution, [status(thm)], [c_32, c_1638])).
% 3.27/1.52  tff(c_1696, plain, (r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_32, c_1694])).
% 3.27/1.52  tff(c_1700, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1564, c_1696])).
% 3.27/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.27/1.52  
% 3.27/1.52  Inference rules
% 3.27/1.52  ----------------------
% 3.27/1.52  #Ref     : 0
% 3.27/1.52  #Sup     : 416
% 3.27/1.52  #Fact    : 0
% 3.27/1.52  #Define  : 0
% 3.27/1.52  #Split   : 0
% 3.27/1.52  #Chain   : 0
% 3.27/1.52  #Close   : 0
% 3.27/1.52  
% 3.27/1.52  Ordering : KBO
% 3.27/1.52  
% 3.27/1.52  Simplification rules
% 3.27/1.52  ----------------------
% 3.27/1.52  #Subsume      : 3
% 3.27/1.52  #Demod        : 343
% 3.27/1.52  #Tautology    : 304
% 3.27/1.52  #SimpNegUnit  : 1
% 3.27/1.52  #BackRed      : 1
% 3.27/1.52  
% 3.27/1.52  #Partial instantiations: 0
% 3.27/1.52  #Strategies tried      : 1
% 3.27/1.52  
% 3.27/1.52  Timing (in seconds)
% 3.27/1.52  ----------------------
% 3.27/1.52  Preprocessing        : 0.30
% 3.27/1.52  Parsing              : 0.17
% 3.27/1.52  CNF conversion       : 0.02
% 3.27/1.52  Main loop            : 0.43
% 3.27/1.52  Inferencing          : 0.14
% 3.27/1.52  Reduction            : 0.18
% 3.27/1.52  Demodulation         : 0.15
% 3.27/1.53  BG Simplification    : 0.02
% 3.27/1.53  Subsumption          : 0.06
% 3.27/1.53  Abstraction          : 0.02
% 3.27/1.53  MUC search           : 0.00
% 3.27/1.53  Cooper               : 0.00
% 3.27/1.53  Total                : 0.76
% 3.27/1.53  Index Insertion      : 0.00
% 3.27/1.53  Index Deletion       : 0.00
% 3.27/1.53  Index Matching       : 0.00
% 3.27/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
