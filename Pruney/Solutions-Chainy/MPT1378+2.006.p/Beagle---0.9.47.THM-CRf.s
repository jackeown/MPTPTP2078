%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:04 EST 2020

% Result     : Theorem 33.92s
% Output     : CNFRefutation 34.25s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 154 expanded)
%              Number of leaves         :   28 (  68 expanded)
%              Depth                    :   14
%              Number of atoms          :  138 ( 558 expanded)
%              Number of equality atoms :    5 (  17 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k4_subset_1 > k2_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                   => ( ( m1_connsp_2(C,A,B)
                        & m1_connsp_2(D,A,B) )
                     => m1_connsp_2(k4_subset_1(u1_struct_0(A),C,D),A,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_connsp_2)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_83,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m1_connsp_2(C,A,B)
              <=> r2_hidden(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_36,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_28,plain,(
    m1_connsp_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_40,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_38,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_97,plain,(
    ! [A_68,B_69,C_70] :
      ( k4_subset_1(A_68,B_69,C_70) = k2_xboole_0(B_69,C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(A_68))
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_185,plain,(
    ! [B_75] :
      ( k4_subset_1(u1_struct_0('#skF_2'),B_75,'#skF_5') = k2_xboole_0(B_75,'#skF_5')
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_32,c_97])).

tff(c_209,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_4','#skF_5') = k2_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_185])).

tff(c_16,plain,(
    ! [A_11,B_12,C_13] :
      ( m1_subset_1(k4_subset_1(A_11,B_12,C_13),k1_zfmisc_1(A_11))
      | ~ m1_subset_1(C_13,k1_zfmisc_1(A_11))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_215,plain,
    ( m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_16])).

tff(c_219,plain,(
    m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_215])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_14,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_tarski(A_8,k2_xboole_0(C_10,B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_20,plain,(
    ! [A_17,B_21,C_23] :
      ( r1_tarski(k1_tops_1(A_17,B_21),k1_tops_1(A_17,C_23))
      | ~ r1_tarski(B_21,C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_252,plain,(
    ! [B_76,A_77,C_78] :
      ( r2_hidden(B_76,k1_tops_1(A_77,C_78))
      | ~ m1_connsp_2(C_78,A_77,B_76)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ m1_subset_1(B_76,u1_struct_0(A_77))
      | ~ l1_pre_topc(A_77)
      | ~ v2_pre_topc(A_77)
      | v2_struct_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_269,plain,(
    ! [B_76] :
      ( r2_hidden(B_76,k1_tops_1('#skF_2','#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_2',B_76)
      | ~ m1_subset_1(B_76,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_32,c_252])).

tff(c_297,plain,(
    ! [B_76] :
      ( r2_hidden(B_76,k1_tops_1('#skF_2','#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_2',B_76)
      | ~ m1_subset_1(B_76,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_269])).

tff(c_470,plain,(
    ! [B_83] :
      ( r2_hidden(B_83,k1_tops_1('#skF_2','#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_2',B_83)
      | ~ m1_subset_1(B_83,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_297])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_587,plain,(
    ! [B_97,B_98] :
      ( r2_hidden(B_97,B_98)
      | ~ r1_tarski(k1_tops_1('#skF_2','#skF_5'),B_98)
      | ~ m1_connsp_2('#skF_5','#skF_2',B_97)
      | ~ m1_subset_1(B_97,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_470,c_2])).

tff(c_590,plain,(
    ! [B_97,C_23] :
      ( r2_hidden(B_97,k1_tops_1('#skF_2',C_23))
      | ~ m1_connsp_2('#skF_5','#skF_2',B_97)
      | ~ m1_subset_1(B_97,u1_struct_0('#skF_2'))
      | ~ r1_tarski('#skF_5',C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_20,c_587])).

tff(c_8426,plain,(
    ! [B_189,C_190] :
      ( r2_hidden(B_189,k1_tops_1('#skF_2',C_190))
      | ~ m1_connsp_2('#skF_5','#skF_2',B_189)
      | ~ m1_subset_1(B_189,u1_struct_0('#skF_2'))
      | ~ r1_tarski('#skF_5',C_190)
      | ~ m1_subset_1(C_190,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32,c_590])).

tff(c_8661,plain,(
    ! [B_189] :
      ( r2_hidden(B_189,k1_tops_1('#skF_2',k2_xboole_0('#skF_4','#skF_5')))
      | ~ m1_connsp_2('#skF_5','#skF_2',B_189)
      | ~ m1_subset_1(B_189,u1_struct_0('#skF_2'))
      | ~ r1_tarski('#skF_5',k2_xboole_0('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_219,c_8426])).

tff(c_53385,plain,(
    ~ r1_tarski('#skF_5',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_8661])).

tff(c_53388,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_14,c_53385])).

tff(c_53392,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_53388])).

tff(c_53983,plain,(
    ! [B_580] :
      ( r2_hidden(B_580,k1_tops_1('#skF_2',k2_xboole_0('#skF_4','#skF_5')))
      | ~ m1_connsp_2('#skF_5','#skF_2',B_580)
      | ~ m1_subset_1(B_580,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_8661])).

tff(c_22,plain,(
    ! [C_30,A_24,B_28] :
      ( m1_connsp_2(C_30,A_24,B_28)
      | ~ r2_hidden(B_28,k1_tops_1(A_24,C_30))
      | ~ m1_subset_1(C_30,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ m1_subset_1(B_28,u1_struct_0(A_24))
      | ~ l1_pre_topc(A_24)
      | ~ v2_pre_topc(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_53985,plain,(
    ! [B_580] :
      ( m1_connsp_2(k2_xboole_0('#skF_4','#skF_5'),'#skF_2',B_580)
      | ~ m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_connsp_2('#skF_5','#skF_2',B_580)
      | ~ m1_subset_1(B_580,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_53983,c_22])).

tff(c_53994,plain,(
    ! [B_580] :
      ( m1_connsp_2(k2_xboole_0('#skF_4','#skF_5'),'#skF_2',B_580)
      | v2_struct_0('#skF_2')
      | ~ m1_connsp_2('#skF_5','#skF_2',B_580)
      | ~ m1_subset_1(B_580,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_219,c_53985])).

tff(c_53998,plain,(
    ! [B_581] :
      ( m1_connsp_2(k2_xboole_0('#skF_4','#skF_5'),'#skF_2',B_581)
      | ~ m1_connsp_2('#skF_5','#skF_2',B_581)
      | ~ m1_subset_1(B_581,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_53994])).

tff(c_26,plain,(
    ~ m1_connsp_2(k4_subset_1(u1_struct_0('#skF_2'),'#skF_4','#skF_5'),'#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_211,plain,(
    ~ m1_connsp_2(k2_xboole_0('#skF_4','#skF_5'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_26])).

tff(c_54006,plain,
    ( ~ m1_connsp_2('#skF_5','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_53998,c_211])).

tff(c_54012,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_28,c_54006])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:40:19 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 33.92/22.03  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 34.25/22.03  
% 34.25/22.03  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 34.25/22.03  %$ m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k4_subset_1 > k2_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 34.25/22.03  
% 34.25/22.03  %Foreground sorts:
% 34.25/22.03  
% 34.25/22.03  
% 34.25/22.03  %Background operators:
% 34.25/22.03  
% 34.25/22.03  
% 34.25/22.03  %Foreground operators:
% 34.25/22.03  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 34.25/22.03  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 34.25/22.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 34.25/22.03  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 34.25/22.03  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 34.25/22.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 34.25/22.03  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 34.25/22.03  tff('#skF_5', type, '#skF_5': $i).
% 34.25/22.03  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 34.25/22.03  tff('#skF_2', type, '#skF_2': $i).
% 34.25/22.03  tff('#skF_3', type, '#skF_3': $i).
% 34.25/22.03  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 34.25/22.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 34.25/22.03  tff('#skF_4', type, '#skF_4': $i).
% 34.25/22.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 34.25/22.03  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 34.25/22.03  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 34.25/22.03  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 34.25/22.03  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 34.25/22.03  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 34.25/22.03  
% 34.25/22.05  tff(f_106, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ((m1_connsp_2(C, A, B) & m1_connsp_2(D, A, B)) => m1_connsp_2(k4_subset_1(u1_struct_0(A), C, D), A, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_connsp_2)).
% 34.25/22.05  tff(f_54, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 34.25/22.05  tff(f_48, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 34.25/22.05  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 34.25/22.05  tff(f_42, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 34.25/22.05  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 34.25/22.05  tff(f_83, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_connsp_2)).
% 34.25/22.05  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 34.25/22.05  tff(c_36, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 34.25/22.05  tff(c_28, plain, (m1_connsp_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 34.25/22.05  tff(c_42, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_106])).
% 34.25/22.05  tff(c_40, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_106])).
% 34.25/22.05  tff(c_38, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_106])).
% 34.25/22.05  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 34.25/22.05  tff(c_32, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 34.25/22.05  tff(c_97, plain, (![A_68, B_69, C_70]: (k4_subset_1(A_68, B_69, C_70)=k2_xboole_0(B_69, C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(A_68)) | ~m1_subset_1(B_69, k1_zfmisc_1(A_68)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 34.25/22.05  tff(c_185, plain, (![B_75]: (k4_subset_1(u1_struct_0('#skF_2'), B_75, '#skF_5')=k2_xboole_0(B_75, '#skF_5') | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_32, c_97])).
% 34.25/22.05  tff(c_209, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_4', '#skF_5')=k2_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_34, c_185])).
% 34.25/22.05  tff(c_16, plain, (![A_11, B_12, C_13]: (m1_subset_1(k4_subset_1(A_11, B_12, C_13), k1_zfmisc_1(A_11)) | ~m1_subset_1(C_13, k1_zfmisc_1(A_11)) | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 34.25/22.05  tff(c_215, plain, (m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_209, c_16])).
% 34.25/22.05  tff(c_219, plain, (m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_215])).
% 34.25/22.05  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 34.25/22.05  tff(c_14, plain, (![A_8, C_10, B_9]: (r1_tarski(A_8, k2_xboole_0(C_10, B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 34.25/22.05  tff(c_20, plain, (![A_17, B_21, C_23]: (r1_tarski(k1_tops_1(A_17, B_21), k1_tops_1(A_17, C_23)) | ~r1_tarski(B_21, C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(u1_struct_0(A_17))) | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_66])).
% 34.25/22.05  tff(c_252, plain, (![B_76, A_77, C_78]: (r2_hidden(B_76, k1_tops_1(A_77, C_78)) | ~m1_connsp_2(C_78, A_77, B_76) | ~m1_subset_1(C_78, k1_zfmisc_1(u1_struct_0(A_77))) | ~m1_subset_1(B_76, u1_struct_0(A_77)) | ~l1_pre_topc(A_77) | ~v2_pre_topc(A_77) | v2_struct_0(A_77))), inference(cnfTransformation, [status(thm)], [f_83])).
% 34.25/22.05  tff(c_269, plain, (![B_76]: (r2_hidden(B_76, k1_tops_1('#skF_2', '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_2', B_76) | ~m1_subset_1(B_76, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_252])).
% 34.25/22.05  tff(c_297, plain, (![B_76]: (r2_hidden(B_76, k1_tops_1('#skF_2', '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_2', B_76) | ~m1_subset_1(B_76, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_269])).
% 34.25/22.05  tff(c_470, plain, (![B_83]: (r2_hidden(B_83, k1_tops_1('#skF_2', '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_2', B_83) | ~m1_subset_1(B_83, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_42, c_297])).
% 34.25/22.05  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 34.25/22.05  tff(c_587, plain, (![B_97, B_98]: (r2_hidden(B_97, B_98) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_5'), B_98) | ~m1_connsp_2('#skF_5', '#skF_2', B_97) | ~m1_subset_1(B_97, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_470, c_2])).
% 34.25/22.05  tff(c_590, plain, (![B_97, C_23]: (r2_hidden(B_97, k1_tops_1('#skF_2', C_23)) | ~m1_connsp_2('#skF_5', '#skF_2', B_97) | ~m1_subset_1(B_97, u1_struct_0('#skF_2')) | ~r1_tarski('#skF_5', C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_20, c_587])).
% 34.25/22.05  tff(c_8426, plain, (![B_189, C_190]: (r2_hidden(B_189, k1_tops_1('#skF_2', C_190)) | ~m1_connsp_2('#skF_5', '#skF_2', B_189) | ~m1_subset_1(B_189, u1_struct_0('#skF_2')) | ~r1_tarski('#skF_5', C_190) | ~m1_subset_1(C_190, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32, c_590])).
% 34.25/22.05  tff(c_8661, plain, (![B_189]: (r2_hidden(B_189, k1_tops_1('#skF_2', k2_xboole_0('#skF_4', '#skF_5'))) | ~m1_connsp_2('#skF_5', '#skF_2', B_189) | ~m1_subset_1(B_189, u1_struct_0('#skF_2')) | ~r1_tarski('#skF_5', k2_xboole_0('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_219, c_8426])).
% 34.25/22.05  tff(c_53385, plain, (~r1_tarski('#skF_5', k2_xboole_0('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_8661])).
% 34.25/22.05  tff(c_53388, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_14, c_53385])).
% 34.25/22.05  tff(c_53392, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_53388])).
% 34.25/22.05  tff(c_53983, plain, (![B_580]: (r2_hidden(B_580, k1_tops_1('#skF_2', k2_xboole_0('#skF_4', '#skF_5'))) | ~m1_connsp_2('#skF_5', '#skF_2', B_580) | ~m1_subset_1(B_580, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_8661])).
% 34.25/22.05  tff(c_22, plain, (![C_30, A_24, B_28]: (m1_connsp_2(C_30, A_24, B_28) | ~r2_hidden(B_28, k1_tops_1(A_24, C_30)) | ~m1_subset_1(C_30, k1_zfmisc_1(u1_struct_0(A_24))) | ~m1_subset_1(B_28, u1_struct_0(A_24)) | ~l1_pre_topc(A_24) | ~v2_pre_topc(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_83])).
% 34.25/22.05  tff(c_53985, plain, (![B_580]: (m1_connsp_2(k2_xboole_0('#skF_4', '#skF_5'), '#skF_2', B_580) | ~m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_connsp_2('#skF_5', '#skF_2', B_580) | ~m1_subset_1(B_580, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_53983, c_22])).
% 34.25/22.05  tff(c_53994, plain, (![B_580]: (m1_connsp_2(k2_xboole_0('#skF_4', '#skF_5'), '#skF_2', B_580) | v2_struct_0('#skF_2') | ~m1_connsp_2('#skF_5', '#skF_2', B_580) | ~m1_subset_1(B_580, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_219, c_53985])).
% 34.25/22.05  tff(c_53998, plain, (![B_581]: (m1_connsp_2(k2_xboole_0('#skF_4', '#skF_5'), '#skF_2', B_581) | ~m1_connsp_2('#skF_5', '#skF_2', B_581) | ~m1_subset_1(B_581, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_42, c_53994])).
% 34.25/22.05  tff(c_26, plain, (~m1_connsp_2(k4_subset_1(u1_struct_0('#skF_2'), '#skF_4', '#skF_5'), '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 34.25/22.05  tff(c_211, plain, (~m1_connsp_2(k2_xboole_0('#skF_4', '#skF_5'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_209, c_26])).
% 34.25/22.05  tff(c_54006, plain, (~m1_connsp_2('#skF_5', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_53998, c_211])).
% 34.25/22.05  tff(c_54012, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_28, c_54006])).
% 34.25/22.05  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 34.25/22.05  
% 34.25/22.05  Inference rules
% 34.25/22.05  ----------------------
% 34.25/22.05  #Ref     : 0
% 34.25/22.05  #Sup     : 12036
% 34.25/22.05  #Fact    : 0
% 34.25/22.05  #Define  : 0
% 34.25/22.05  #Split   : 8
% 34.25/22.05  #Chain   : 0
% 34.25/22.05  #Close   : 0
% 34.25/22.05  
% 34.25/22.05  Ordering : KBO
% 34.25/22.05  
% 34.25/22.05  Simplification rules
% 34.25/22.05  ----------------------
% 34.25/22.05  #Subsume      : 166
% 34.25/22.05  #Demod        : 26539
% 34.25/22.05  #Tautology    : 497
% 34.25/22.05  #SimpNegUnit  : 1686
% 34.25/22.05  #BackRed      : 1
% 34.25/22.05  
% 34.25/22.05  #Partial instantiations: 0
% 34.25/22.05  #Strategies tried      : 1
% 34.25/22.05  
% 34.25/22.05  Timing (in seconds)
% 34.25/22.05  ----------------------
% 34.25/22.05  Preprocessing        : 0.32
% 34.25/22.05  Parsing              : 0.17
% 34.25/22.05  CNF conversion       : 0.02
% 34.25/22.05  Main loop            : 20.98
% 34.25/22.05  Inferencing          : 2.03
% 34.25/22.05  Reduction            : 12.11
% 34.25/22.05  Demodulation         : 11.05
% 34.25/22.05  BG Simplification    : 0.23
% 34.25/22.05  Subsumption          : 5.71
% 34.25/22.05  Abstraction          : 0.47
% 34.25/22.05  MUC search           : 0.00
% 34.25/22.05  Cooper               : 0.00
% 34.25/22.05  Total                : 21.33
% 34.25/22.05  Index Insertion      : 0.00
% 34.25/22.05  Index Deletion       : 0.00
% 34.25/22.05  Index Matching       : 0.00
% 34.25/22.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
