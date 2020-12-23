%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:52 EST 2020

% Result     : Theorem 14.43s
% Output     : CNFRefutation 14.43s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 102 expanded)
%              Number of leaves         :   35 (  51 expanded)
%              Depth                    :   11
%              Number of atoms          :  107 ( 175 expanded)
%              Number of equality atoms :   29 (  49 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k3_tarski > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => k9_relat_1(B,k10_relat_1(B,A)) = k3_xboole_0(A,k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] : r1_tarski(k3_xboole_0(A,B),k2_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_xboole_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_45,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_47,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k9_relat_1(B,A) = k9_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_relat_1)).

tff(c_40,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_38,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_30,plain,(
    ! [B_32,A_31] :
      ( k10_relat_1(B_32,k3_xboole_0(k2_relat_1(B_32),A_31)) = k10_relat_1(B_32,A_31)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_128,plain,(
    ! [A_52,B_53,C_54] : r1_tarski(k3_xboole_0(A_52,B_53),k2_xboole_0(A_52,C_54)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_143,plain,(
    ! [A_3,B_53] : r1_tarski(k3_xboole_0(A_3,B_53),A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_128])).

tff(c_1193,plain,(
    ! [B_106,A_107] :
      ( k9_relat_1(B_106,k10_relat_1(B_106,A_107)) = A_107
      | ~ r1_tarski(A_107,k2_relat_1(B_106))
      | ~ v1_funct_1(B_106)
      | ~ v1_relat_1(B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_9098,plain,(
    ! [B_234,B_235] :
      ( k9_relat_1(B_234,k10_relat_1(B_234,k3_xboole_0(k2_relat_1(B_234),B_235))) = k3_xboole_0(k2_relat_1(B_234),B_235)
      | ~ v1_funct_1(B_234)
      | ~ v1_relat_1(B_234) ) ),
    inference(resolution,[status(thm)],[c_143,c_1193])).

tff(c_9165,plain,(
    ! [B_32,A_31] :
      ( k9_relat_1(B_32,k10_relat_1(B_32,A_31)) = k3_xboole_0(k2_relat_1(B_32),A_31)
      | ~ v1_funct_1(B_32)
      | ~ v1_relat_1(B_32)
      | ~ v1_relat_1(B_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_9098])).

tff(c_18,plain,(
    ! [A_23] : k2_subset_1(A_23) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_20,plain,(
    ! [A_24] : m1_subset_1(k2_subset_1(A_24),k1_zfmisc_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_41,plain,(
    ! [A_24] : m1_subset_1(A_24,k1_zfmisc_1(A_24)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20])).

tff(c_103,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(A_44,B_45)
      | ~ m1_subset_1(A_44,k1_zfmisc_1(B_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_107,plain,(
    ! [A_24] : r1_tarski(A_24,A_24) ),
    inference(resolution,[status(thm)],[c_41,c_103])).

tff(c_5204,plain,(
    ! [B_171] :
      ( k9_relat_1(B_171,k10_relat_1(B_171,k2_relat_1(B_171))) = k2_relat_1(B_171)
      | ~ v1_funct_1(B_171)
      | ~ v1_relat_1(B_171) ) ),
    inference(resolution,[status(thm)],[c_107,c_1193])).

tff(c_28,plain,(
    ! [B_30,A_29] :
      ( r1_tarski(k9_relat_1(B_30,A_29),k9_relat_1(B_30,k1_relat_1(B_30)))
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_13350,plain,(
    ! [B_270] :
      ( r1_tarski(k2_relat_1(B_270),k9_relat_1(B_270,k1_relat_1(B_270)))
      | ~ v1_relat_1(B_270)
      | ~ v1_funct_1(B_270)
      | ~ v1_relat_1(B_270) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5204,c_28])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_13354,plain,(
    ! [B_270] :
      ( k3_xboole_0(k2_relat_1(B_270),k9_relat_1(B_270,k1_relat_1(B_270))) = k2_relat_1(B_270)
      | ~ v1_funct_1(B_270)
      | ~ v1_relat_1(B_270) ) ),
    inference(resolution,[status(thm)],[c_13350,c_6])).

tff(c_16929,plain,(
    ! [B_331,A_332] :
      ( k9_relat_1(B_331,k10_relat_1(B_331,A_332)) = k3_xboole_0(k2_relat_1(B_331),A_332)
      | ~ v1_funct_1(B_331)
      | ~ v1_relat_1(B_331)
      | ~ v1_relat_1(B_331) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_9098])).

tff(c_822,plain,(
    ! [A_93,B_94] :
      ( r1_tarski(A_93,k10_relat_1(B_94,k9_relat_1(B_94,A_93)))
      | ~ r1_tarski(A_93,k1_relat_1(B_94))
      | ~ v1_relat_1(B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_5040,plain,(
    ! [A_169,B_170] :
      ( k3_xboole_0(A_169,k10_relat_1(B_170,k9_relat_1(B_170,A_169))) = A_169
      | ~ r1_tarski(A_169,k1_relat_1(B_170))
      | ~ v1_relat_1(B_170) ) ),
    inference(resolution,[status(thm)],[c_822,c_6])).

tff(c_26,plain,(
    ! [B_28,A_27] :
      ( k9_relat_1(B_28,k3_xboole_0(k1_relat_1(B_28),A_27)) = k9_relat_1(B_28,A_27)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_5117,plain,(
    ! [B_28,B_170] :
      ( k9_relat_1(B_28,k10_relat_1(B_170,k9_relat_1(B_170,k1_relat_1(B_28)))) = k9_relat_1(B_28,k1_relat_1(B_28))
      | ~ v1_relat_1(B_28)
      | ~ r1_tarski(k1_relat_1(B_28),k1_relat_1(B_170))
      | ~ v1_relat_1(B_170) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5040,c_26])).

tff(c_16955,plain,(
    ! [B_331] :
      ( k3_xboole_0(k2_relat_1(B_331),k9_relat_1(B_331,k1_relat_1(B_331))) = k9_relat_1(B_331,k1_relat_1(B_331))
      | ~ v1_relat_1(B_331)
      | ~ r1_tarski(k1_relat_1(B_331),k1_relat_1(B_331))
      | ~ v1_relat_1(B_331)
      | ~ v1_funct_1(B_331)
      | ~ v1_relat_1(B_331)
      | ~ v1_relat_1(B_331) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16929,c_5117])).

tff(c_34021,plain,(
    ! [B_489] :
      ( k3_xboole_0(k2_relat_1(B_489),k9_relat_1(B_489,k1_relat_1(B_489))) = k9_relat_1(B_489,k1_relat_1(B_489))
      | ~ v1_funct_1(B_489)
      | ~ v1_relat_1(B_489) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_16955])).

tff(c_34387,plain,(
    ! [B_493] :
      ( k9_relat_1(B_493,k1_relat_1(B_493)) = k2_relat_1(B_493)
      | ~ v1_funct_1(B_493)
      | ~ v1_relat_1(B_493)
      | ~ v1_funct_1(B_493)
      | ~ v1_relat_1(B_493) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13354,c_34021])).

tff(c_36,plain,(
    k3_xboole_0('#skF_1',k9_relat_1('#skF_2',k1_relat_1('#skF_2'))) != k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_34588,plain,
    ( k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1')) != k3_xboole_0('#skF_1',k2_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_34387,c_36])).

tff(c_34646,plain,(
    k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1')) != k3_xboole_0('#skF_1',k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_40,c_38,c_34588])).

tff(c_34650,plain,
    ( k3_xboole_0(k2_relat_1('#skF_2'),'#skF_1') != k3_xboole_0('#skF_1',k2_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_9165,c_34646])).

tff(c_34653,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40,c_38,c_2,c_34650])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:48:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.43/7.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.43/7.07  
% 14.43/7.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.43/7.07  %$ r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k3_tarski > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 14.43/7.07  
% 14.43/7.07  %Foreground sorts:
% 14.43/7.07  
% 14.43/7.07  
% 14.43/7.07  %Background operators:
% 14.43/7.07  
% 14.43/7.07  
% 14.43/7.07  %Foreground operators:
% 14.43/7.07  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 14.43/7.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.43/7.07  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 14.43/7.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.43/7.07  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 14.43/7.07  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 14.43/7.07  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 14.43/7.07  tff('#skF_2', type, '#skF_2': $i).
% 14.43/7.07  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 14.43/7.07  tff('#skF_1', type, '#skF_1': $i).
% 14.43/7.07  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 14.43/7.07  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.43/7.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.43/7.07  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 14.43/7.07  tff(k3_tarski, type, k3_tarski: $i > $i).
% 14.43/7.07  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 14.43/7.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.43/7.07  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.43/7.07  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 14.43/7.07  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 14.43/7.07  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 14.43/7.07  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.43/7.07  
% 14.43/7.08  tff(f_84, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = k3_xboole_0(A, k9_relat_1(B, k1_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_funct_1)).
% 14.43/7.08  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 14.43/7.08  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 14.43/7.08  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 14.43/7.08  tff(f_35, axiom, (![A, B, C]: r1_tarski(k3_xboole_0(A, B), k2_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_xboole_1)).
% 14.43/7.08  tff(f_77, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 14.43/7.08  tff(f_45, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 14.43/7.08  tff(f_47, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 14.43/7.08  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 14.43/7.08  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k9_relat_1(B, k1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_relat_1)).
% 14.43/7.08  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 14.43/7.08  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 14.43/7.08  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (k9_relat_1(B, A) = k9_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_relat_1)).
% 14.43/7.08  tff(c_40, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 14.43/7.08  tff(c_38, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 14.43/7.08  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 14.43/7.08  tff(c_30, plain, (![B_32, A_31]: (k10_relat_1(B_32, k3_xboole_0(k2_relat_1(B_32), A_31))=k10_relat_1(B_32, A_31) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_63])).
% 14.43/7.08  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 14.43/7.08  tff(c_128, plain, (![A_52, B_53, C_54]: (r1_tarski(k3_xboole_0(A_52, B_53), k2_xboole_0(A_52, C_54)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 14.43/7.08  tff(c_143, plain, (![A_3, B_53]: (r1_tarski(k3_xboole_0(A_3, B_53), A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_128])).
% 14.43/7.08  tff(c_1193, plain, (![B_106, A_107]: (k9_relat_1(B_106, k10_relat_1(B_106, A_107))=A_107 | ~r1_tarski(A_107, k2_relat_1(B_106)) | ~v1_funct_1(B_106) | ~v1_relat_1(B_106))), inference(cnfTransformation, [status(thm)], [f_77])).
% 14.43/7.08  tff(c_9098, plain, (![B_234, B_235]: (k9_relat_1(B_234, k10_relat_1(B_234, k3_xboole_0(k2_relat_1(B_234), B_235)))=k3_xboole_0(k2_relat_1(B_234), B_235) | ~v1_funct_1(B_234) | ~v1_relat_1(B_234))), inference(resolution, [status(thm)], [c_143, c_1193])).
% 14.43/7.08  tff(c_9165, plain, (![B_32, A_31]: (k9_relat_1(B_32, k10_relat_1(B_32, A_31))=k3_xboole_0(k2_relat_1(B_32), A_31) | ~v1_funct_1(B_32) | ~v1_relat_1(B_32) | ~v1_relat_1(B_32))), inference(superposition, [status(thm), theory('equality')], [c_30, c_9098])).
% 14.43/7.08  tff(c_18, plain, (![A_23]: (k2_subset_1(A_23)=A_23)), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.43/7.08  tff(c_20, plain, (![A_24]: (m1_subset_1(k2_subset_1(A_24), k1_zfmisc_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.43/7.08  tff(c_41, plain, (![A_24]: (m1_subset_1(A_24, k1_zfmisc_1(A_24)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_20])).
% 14.43/7.08  tff(c_103, plain, (![A_44, B_45]: (r1_tarski(A_44, B_45) | ~m1_subset_1(A_44, k1_zfmisc_1(B_45)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 14.43/7.08  tff(c_107, plain, (![A_24]: (r1_tarski(A_24, A_24))), inference(resolution, [status(thm)], [c_41, c_103])).
% 14.43/7.08  tff(c_5204, plain, (![B_171]: (k9_relat_1(B_171, k10_relat_1(B_171, k2_relat_1(B_171)))=k2_relat_1(B_171) | ~v1_funct_1(B_171) | ~v1_relat_1(B_171))), inference(resolution, [status(thm)], [c_107, c_1193])).
% 14.43/7.08  tff(c_28, plain, (![B_30, A_29]: (r1_tarski(k9_relat_1(B_30, A_29), k9_relat_1(B_30, k1_relat_1(B_30))) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_59])).
% 14.43/7.08  tff(c_13350, plain, (![B_270]: (r1_tarski(k2_relat_1(B_270), k9_relat_1(B_270, k1_relat_1(B_270))) | ~v1_relat_1(B_270) | ~v1_funct_1(B_270) | ~v1_relat_1(B_270))), inference(superposition, [status(thm), theory('equality')], [c_5204, c_28])).
% 14.43/7.08  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 14.43/7.08  tff(c_13354, plain, (![B_270]: (k3_xboole_0(k2_relat_1(B_270), k9_relat_1(B_270, k1_relat_1(B_270)))=k2_relat_1(B_270) | ~v1_funct_1(B_270) | ~v1_relat_1(B_270))), inference(resolution, [status(thm)], [c_13350, c_6])).
% 14.43/7.08  tff(c_16929, plain, (![B_331, A_332]: (k9_relat_1(B_331, k10_relat_1(B_331, A_332))=k3_xboole_0(k2_relat_1(B_331), A_332) | ~v1_funct_1(B_331) | ~v1_relat_1(B_331) | ~v1_relat_1(B_331))), inference(superposition, [status(thm), theory('equality')], [c_30, c_9098])).
% 14.43/7.08  tff(c_822, plain, (![A_93, B_94]: (r1_tarski(A_93, k10_relat_1(B_94, k9_relat_1(B_94, A_93))) | ~r1_tarski(A_93, k1_relat_1(B_94)) | ~v1_relat_1(B_94))), inference(cnfTransformation, [status(thm)], [f_69])).
% 14.43/7.08  tff(c_5040, plain, (![A_169, B_170]: (k3_xboole_0(A_169, k10_relat_1(B_170, k9_relat_1(B_170, A_169)))=A_169 | ~r1_tarski(A_169, k1_relat_1(B_170)) | ~v1_relat_1(B_170))), inference(resolution, [status(thm)], [c_822, c_6])).
% 14.43/7.08  tff(c_26, plain, (![B_28, A_27]: (k9_relat_1(B_28, k3_xboole_0(k1_relat_1(B_28), A_27))=k9_relat_1(B_28, A_27) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_55])).
% 14.43/7.08  tff(c_5117, plain, (![B_28, B_170]: (k9_relat_1(B_28, k10_relat_1(B_170, k9_relat_1(B_170, k1_relat_1(B_28))))=k9_relat_1(B_28, k1_relat_1(B_28)) | ~v1_relat_1(B_28) | ~r1_tarski(k1_relat_1(B_28), k1_relat_1(B_170)) | ~v1_relat_1(B_170))), inference(superposition, [status(thm), theory('equality')], [c_5040, c_26])).
% 14.43/7.08  tff(c_16955, plain, (![B_331]: (k3_xboole_0(k2_relat_1(B_331), k9_relat_1(B_331, k1_relat_1(B_331)))=k9_relat_1(B_331, k1_relat_1(B_331)) | ~v1_relat_1(B_331) | ~r1_tarski(k1_relat_1(B_331), k1_relat_1(B_331)) | ~v1_relat_1(B_331) | ~v1_funct_1(B_331) | ~v1_relat_1(B_331) | ~v1_relat_1(B_331))), inference(superposition, [status(thm), theory('equality')], [c_16929, c_5117])).
% 14.43/7.08  tff(c_34021, plain, (![B_489]: (k3_xboole_0(k2_relat_1(B_489), k9_relat_1(B_489, k1_relat_1(B_489)))=k9_relat_1(B_489, k1_relat_1(B_489)) | ~v1_funct_1(B_489) | ~v1_relat_1(B_489))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_16955])).
% 14.43/7.08  tff(c_34387, plain, (![B_493]: (k9_relat_1(B_493, k1_relat_1(B_493))=k2_relat_1(B_493) | ~v1_funct_1(B_493) | ~v1_relat_1(B_493) | ~v1_funct_1(B_493) | ~v1_relat_1(B_493))), inference(superposition, [status(thm), theory('equality')], [c_13354, c_34021])).
% 14.43/7.08  tff(c_36, plain, (k3_xboole_0('#skF_1', k9_relat_1('#skF_2', k1_relat_1('#skF_2')))!=k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 14.43/7.08  tff(c_34588, plain, (k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1'))!=k3_xboole_0('#skF_1', k2_relat_1('#skF_2')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_34387, c_36])).
% 14.43/7.08  tff(c_34646, plain, (k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1'))!=k3_xboole_0('#skF_1', k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_40, c_38, c_34588])).
% 14.43/7.08  tff(c_34650, plain, (k3_xboole_0(k2_relat_1('#skF_2'), '#skF_1')!=k3_xboole_0('#skF_1', k2_relat_1('#skF_2')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_9165, c_34646])).
% 14.43/7.08  tff(c_34653, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_40, c_38, c_2, c_34650])).
% 14.43/7.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.43/7.08  
% 14.43/7.08  Inference rules
% 14.43/7.08  ----------------------
% 14.43/7.08  #Ref     : 0
% 14.43/7.08  #Sup     : 8624
% 14.43/7.08  #Fact    : 0
% 14.43/7.08  #Define  : 0
% 14.43/7.08  #Split   : 0
% 14.43/7.08  #Chain   : 0
% 14.43/7.08  #Close   : 0
% 14.43/7.08  
% 14.43/7.08  Ordering : KBO
% 14.43/7.08  
% 14.43/7.08  Simplification rules
% 14.43/7.08  ----------------------
% 14.43/7.08  #Subsume      : 1559
% 14.43/7.08  #Demod        : 14099
% 14.43/7.08  #Tautology    : 4758
% 14.43/7.08  #SimpNegUnit  : 0
% 14.43/7.08  #BackRed      : 0
% 14.43/7.08  
% 14.43/7.08  #Partial instantiations: 0
% 14.43/7.08  #Strategies tried      : 1
% 14.43/7.08  
% 14.43/7.08  Timing (in seconds)
% 14.43/7.08  ----------------------
% 14.43/7.09  Preprocessing        : 0.31
% 14.43/7.09  Parsing              : 0.17
% 14.43/7.09  CNF conversion       : 0.02
% 14.43/7.09  Main loop            : 5.98
% 14.43/7.09  Inferencing          : 1.12
% 14.43/7.09  Reduction            : 3.78
% 14.43/7.09  Demodulation         : 3.49
% 14.43/7.09  BG Simplification    : 0.12
% 14.43/7.09  Subsumption          : 0.77
% 14.43/7.09  Abstraction          : 0.35
% 14.43/7.09  MUC search           : 0.00
% 14.43/7.09  Cooper               : 0.00
% 14.43/7.09  Total                : 6.33
% 14.43/7.09  Index Insertion      : 0.00
% 14.43/7.09  Index Deletion       : 0.00
% 14.43/7.09  Index Matching       : 0.00
% 14.43/7.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
