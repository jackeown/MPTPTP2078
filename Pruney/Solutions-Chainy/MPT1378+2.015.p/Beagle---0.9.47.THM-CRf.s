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
% DateTime   : Thu Dec  3 10:24:05 EST 2020

% Result     : Theorem 9.73s
% Output     : CNFRefutation 9.73s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 114 expanded)
%              Number of leaves         :   31 (  56 expanded)
%              Depth                    :   14
%              Number of atoms          :  134 ( 372 expanded)
%              Number of equality atoms :    4 (  12 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k4_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(f_118,negated_conjecture,(
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

tff(f_52,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_34,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_81,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_28,plain,(
    m1_connsp_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_40,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_38,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_146,plain,(
    ! [A_91,B_92,C_93] :
      ( k4_subset_1(A_91,B_92,C_93) = k2_xboole_0(B_92,C_93)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(A_91))
      | ~ m1_subset_1(B_92,k1_zfmisc_1(A_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_174,plain,(
    ! [B_101] :
      ( k4_subset_1(u1_struct_0('#skF_2'),B_101,'#skF_5') = k2_xboole_0(B_101,'#skF_5')
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_32,c_146])).

tff(c_186,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_4','#skF_5') = k2_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_174])).

tff(c_14,plain,(
    ! [A_13,B_14,C_15] :
      ( m1_subset_1(k4_subset_1(A_13,B_14,C_15),k1_zfmisc_1(A_13))
      | ~ m1_subset_1(C_15,k1_zfmisc_1(A_13))
      | ~ m1_subset_1(B_14,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_192,plain,
    ( m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_14])).

tff(c_196,plain,(
    m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_192])).

tff(c_8,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_65,plain,(
    ! [A_60,B_61,C_62] :
      ( r1_tarski(A_60,k2_xboole_0(B_61,C_62))
      | ~ r1_tarski(k4_xboole_0(A_60,B_61),C_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_74,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(B_7,A_6)) ),
    inference(resolution,[status(thm)],[c_8,c_65])).

tff(c_18,plain,(
    ! [A_19,B_23,C_25] :
      ( r1_tarski(k1_tops_1(A_19,B_23),k1_tops_1(A_19,C_25))
      | ~ r1_tarski(B_23,C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_440,plain,(
    ! [B_109,A_110,C_111] :
      ( r2_hidden(B_109,k1_tops_1(A_110,C_111))
      | ~ m1_connsp_2(C_111,A_110,B_109)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ m1_subset_1(B_109,u1_struct_0(A_110))
      | ~ l1_pre_topc(A_110)
      | ~ v2_pre_topc(A_110)
      | v2_struct_0(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_469,plain,(
    ! [B_109] :
      ( r2_hidden(B_109,k1_tops_1('#skF_2','#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_2',B_109)
      | ~ m1_subset_1(B_109,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_32,c_440])).

tff(c_521,plain,(
    ! [B_109] :
      ( r2_hidden(B_109,k1_tops_1('#skF_2','#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_2',B_109)
      | ~ m1_subset_1(B_109,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_469])).

tff(c_558,plain,(
    ! [B_113] :
      ( r2_hidden(B_113,k1_tops_1('#skF_2','#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_2',B_113)
      | ~ m1_subset_1(B_113,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_521])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_747,plain,(
    ! [B_151,B_152] :
      ( r2_hidden(B_151,B_152)
      | ~ r1_tarski(k1_tops_1('#skF_2','#skF_5'),B_152)
      | ~ m1_connsp_2('#skF_5','#skF_2',B_151)
      | ~ m1_subset_1(B_151,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_558,c_2])).

tff(c_759,plain,(
    ! [B_151,C_25] :
      ( r2_hidden(B_151,k1_tops_1('#skF_2',C_25))
      | ~ m1_connsp_2('#skF_5','#skF_2',B_151)
      | ~ m1_subset_1(B_151,u1_struct_0('#skF_2'))
      | ~ r1_tarski('#skF_5',C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_18,c_747])).

tff(c_8672,plain,(
    ! [B_335,C_336] :
      ( r2_hidden(B_335,k1_tops_1('#skF_2',C_336))
      | ~ m1_connsp_2('#skF_5','#skF_2',B_335)
      | ~ m1_subset_1(B_335,u1_struct_0('#skF_2'))
      | ~ r1_tarski('#skF_5',C_336)
      | ~ m1_subset_1(C_336,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32,c_759])).

tff(c_8812,plain,(
    ! [B_335] :
      ( r2_hidden(B_335,k1_tops_1('#skF_2',k2_xboole_0('#skF_4','#skF_5')))
      | ~ m1_connsp_2('#skF_5','#skF_2',B_335)
      | ~ m1_subset_1(B_335,u1_struct_0('#skF_2'))
      | ~ r1_tarski('#skF_5',k2_xboole_0('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_196,c_8672])).

tff(c_9022,plain,(
    ! [B_339] :
      ( r2_hidden(B_339,k1_tops_1('#skF_2',k2_xboole_0('#skF_4','#skF_5')))
      | ~ m1_connsp_2('#skF_5','#skF_2',B_339)
      | ~ m1_subset_1(B_339,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_8812])).

tff(c_20,plain,(
    ! [C_32,A_26,B_30] :
      ( m1_connsp_2(C_32,A_26,B_30)
      | ~ r2_hidden(B_30,k1_tops_1(A_26,C_32))
      | ~ m1_subset_1(C_32,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ m1_subset_1(B_30,u1_struct_0(A_26))
      | ~ l1_pre_topc(A_26)
      | ~ v2_pre_topc(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_9024,plain,(
    ! [B_339] :
      ( m1_connsp_2(k2_xboole_0('#skF_4','#skF_5'),'#skF_2',B_339)
      | ~ m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_connsp_2('#skF_5','#skF_2',B_339)
      | ~ m1_subset_1(B_339,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_9022,c_20])).

tff(c_9033,plain,(
    ! [B_339] :
      ( m1_connsp_2(k2_xboole_0('#skF_4','#skF_5'),'#skF_2',B_339)
      | v2_struct_0('#skF_2')
      | ~ m1_connsp_2('#skF_5','#skF_2',B_339)
      | ~ m1_subset_1(B_339,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_196,c_9024])).

tff(c_9037,plain,(
    ! [B_340] :
      ( m1_connsp_2(k2_xboole_0('#skF_4','#skF_5'),'#skF_2',B_340)
      | ~ m1_connsp_2('#skF_5','#skF_2',B_340)
      | ~ m1_subset_1(B_340,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_9033])).

tff(c_26,plain,(
    ~ m1_connsp_2(k4_subset_1(u1_struct_0('#skF_2'),'#skF_4','#skF_5'),'#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_188,plain,(
    ~ m1_connsp_2(k2_xboole_0('#skF_4','#skF_5'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_26])).

tff(c_9042,plain,
    ( ~ m1_connsp_2('#skF_5','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_9037,c_188])).

tff(c_9050,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_28,c_9042])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:34:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.73/3.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.73/3.44  
% 9.73/3.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.73/3.45  %$ m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k4_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 9.73/3.45  
% 9.73/3.45  %Foreground sorts:
% 9.73/3.45  
% 9.73/3.45  
% 9.73/3.45  %Background operators:
% 9.73/3.45  
% 9.73/3.45  
% 9.73/3.45  %Foreground operators:
% 9.73/3.45  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 9.73/3.45  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 9.73/3.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.73/3.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.73/3.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.73/3.45  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.73/3.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.73/3.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.73/3.45  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 9.73/3.45  tff('#skF_5', type, '#skF_5': $i).
% 9.73/3.45  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 9.73/3.45  tff('#skF_2', type, '#skF_2': $i).
% 9.73/3.45  tff('#skF_3', type, '#skF_3': $i).
% 9.73/3.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.73/3.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.73/3.45  tff(k3_tarski, type, k3_tarski: $i > $i).
% 9.73/3.45  tff('#skF_4', type, '#skF_4': $i).
% 9.73/3.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.73/3.45  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 9.73/3.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.73/3.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.73/3.45  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.73/3.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.73/3.45  
% 9.73/3.46  tff(f_118, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ((m1_connsp_2(C, A, B) & m1_connsp_2(D, A, B)) => m1_connsp_2(k4_subset_1(u1_struct_0(A), C, D), A, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_connsp_2)).
% 9.73/3.46  tff(f_52, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 9.73/3.46  tff(f_46, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 9.73/3.46  tff(f_34, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 9.73/3.46  tff(f_38, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 9.73/3.46  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 9.73/3.46  tff(f_81, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_connsp_2)).
% 9.73/3.46  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 9.73/3.46  tff(c_36, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 9.73/3.46  tff(c_28, plain, (m1_connsp_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 9.73/3.46  tff(c_42, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 9.73/3.46  tff(c_40, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 9.73/3.46  tff(c_38, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 9.73/3.46  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 9.73/3.46  tff(c_32, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 9.73/3.46  tff(c_146, plain, (![A_91, B_92, C_93]: (k4_subset_1(A_91, B_92, C_93)=k2_xboole_0(B_92, C_93) | ~m1_subset_1(C_93, k1_zfmisc_1(A_91)) | ~m1_subset_1(B_92, k1_zfmisc_1(A_91)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.73/3.46  tff(c_174, plain, (![B_101]: (k4_subset_1(u1_struct_0('#skF_2'), B_101, '#skF_5')=k2_xboole_0(B_101, '#skF_5') | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_32, c_146])).
% 9.73/3.46  tff(c_186, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_4', '#skF_5')=k2_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_34, c_174])).
% 9.73/3.46  tff(c_14, plain, (![A_13, B_14, C_15]: (m1_subset_1(k4_subset_1(A_13, B_14, C_15), k1_zfmisc_1(A_13)) | ~m1_subset_1(C_15, k1_zfmisc_1(A_13)) | ~m1_subset_1(B_14, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.73/3.46  tff(c_192, plain, (m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_186, c_14])).
% 9.73/3.46  tff(c_196, plain, (m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_192])).
% 9.73/3.46  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.73/3.46  tff(c_65, plain, (![A_60, B_61, C_62]: (r1_tarski(A_60, k2_xboole_0(B_61, C_62)) | ~r1_tarski(k4_xboole_0(A_60, B_61), C_62))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.73/3.46  tff(c_74, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(B_7, A_6)))), inference(resolution, [status(thm)], [c_8, c_65])).
% 9.73/3.46  tff(c_18, plain, (![A_19, B_23, C_25]: (r1_tarski(k1_tops_1(A_19, B_23), k1_tops_1(A_19, C_25)) | ~r1_tarski(B_23, C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(u1_struct_0(A_19))) | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.73/3.46  tff(c_440, plain, (![B_109, A_110, C_111]: (r2_hidden(B_109, k1_tops_1(A_110, C_111)) | ~m1_connsp_2(C_111, A_110, B_109) | ~m1_subset_1(C_111, k1_zfmisc_1(u1_struct_0(A_110))) | ~m1_subset_1(B_109, u1_struct_0(A_110)) | ~l1_pre_topc(A_110) | ~v2_pre_topc(A_110) | v2_struct_0(A_110))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.73/3.46  tff(c_469, plain, (![B_109]: (r2_hidden(B_109, k1_tops_1('#skF_2', '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_2', B_109) | ~m1_subset_1(B_109, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_440])).
% 9.73/3.46  tff(c_521, plain, (![B_109]: (r2_hidden(B_109, k1_tops_1('#skF_2', '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_2', B_109) | ~m1_subset_1(B_109, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_469])).
% 9.73/3.46  tff(c_558, plain, (![B_113]: (r2_hidden(B_113, k1_tops_1('#skF_2', '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_2', B_113) | ~m1_subset_1(B_113, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_42, c_521])).
% 9.73/3.46  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.73/3.46  tff(c_747, plain, (![B_151, B_152]: (r2_hidden(B_151, B_152) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_5'), B_152) | ~m1_connsp_2('#skF_5', '#skF_2', B_151) | ~m1_subset_1(B_151, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_558, c_2])).
% 9.73/3.46  tff(c_759, plain, (![B_151, C_25]: (r2_hidden(B_151, k1_tops_1('#skF_2', C_25)) | ~m1_connsp_2('#skF_5', '#skF_2', B_151) | ~m1_subset_1(B_151, u1_struct_0('#skF_2')) | ~r1_tarski('#skF_5', C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_18, c_747])).
% 9.73/3.46  tff(c_8672, plain, (![B_335, C_336]: (r2_hidden(B_335, k1_tops_1('#skF_2', C_336)) | ~m1_connsp_2('#skF_5', '#skF_2', B_335) | ~m1_subset_1(B_335, u1_struct_0('#skF_2')) | ~r1_tarski('#skF_5', C_336) | ~m1_subset_1(C_336, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32, c_759])).
% 9.73/3.46  tff(c_8812, plain, (![B_335]: (r2_hidden(B_335, k1_tops_1('#skF_2', k2_xboole_0('#skF_4', '#skF_5'))) | ~m1_connsp_2('#skF_5', '#skF_2', B_335) | ~m1_subset_1(B_335, u1_struct_0('#skF_2')) | ~r1_tarski('#skF_5', k2_xboole_0('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_196, c_8672])).
% 9.73/3.46  tff(c_9022, plain, (![B_339]: (r2_hidden(B_339, k1_tops_1('#skF_2', k2_xboole_0('#skF_4', '#skF_5'))) | ~m1_connsp_2('#skF_5', '#skF_2', B_339) | ~m1_subset_1(B_339, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_8812])).
% 9.73/3.46  tff(c_20, plain, (![C_32, A_26, B_30]: (m1_connsp_2(C_32, A_26, B_30) | ~r2_hidden(B_30, k1_tops_1(A_26, C_32)) | ~m1_subset_1(C_32, k1_zfmisc_1(u1_struct_0(A_26))) | ~m1_subset_1(B_30, u1_struct_0(A_26)) | ~l1_pre_topc(A_26) | ~v2_pre_topc(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.73/3.46  tff(c_9024, plain, (![B_339]: (m1_connsp_2(k2_xboole_0('#skF_4', '#skF_5'), '#skF_2', B_339) | ~m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_connsp_2('#skF_5', '#skF_2', B_339) | ~m1_subset_1(B_339, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_9022, c_20])).
% 9.73/3.46  tff(c_9033, plain, (![B_339]: (m1_connsp_2(k2_xboole_0('#skF_4', '#skF_5'), '#skF_2', B_339) | v2_struct_0('#skF_2') | ~m1_connsp_2('#skF_5', '#skF_2', B_339) | ~m1_subset_1(B_339, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_196, c_9024])).
% 9.73/3.46  tff(c_9037, plain, (![B_340]: (m1_connsp_2(k2_xboole_0('#skF_4', '#skF_5'), '#skF_2', B_340) | ~m1_connsp_2('#skF_5', '#skF_2', B_340) | ~m1_subset_1(B_340, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_42, c_9033])).
% 9.73/3.46  tff(c_26, plain, (~m1_connsp_2(k4_subset_1(u1_struct_0('#skF_2'), '#skF_4', '#skF_5'), '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 9.73/3.46  tff(c_188, plain, (~m1_connsp_2(k2_xboole_0('#skF_4', '#skF_5'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_186, c_26])).
% 9.73/3.46  tff(c_9042, plain, (~m1_connsp_2('#skF_5', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_9037, c_188])).
% 9.73/3.46  tff(c_9050, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_28, c_9042])).
% 9.73/3.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.73/3.46  
% 9.73/3.46  Inference rules
% 9.73/3.46  ----------------------
% 9.73/3.46  #Ref     : 0
% 9.73/3.46  #Sup     : 1986
% 9.73/3.46  #Fact    : 0
% 9.73/3.46  #Define  : 0
% 9.73/3.46  #Split   : 2
% 9.73/3.46  #Chain   : 0
% 9.73/3.46  #Close   : 0
% 9.73/3.46  
% 9.73/3.46  Ordering : KBO
% 9.73/3.46  
% 9.73/3.46  Simplification rules
% 9.73/3.46  ----------------------
% 9.73/3.46  #Subsume      : 23
% 9.73/3.46  #Demod        : 3686
% 9.73/3.46  #Tautology    : 206
% 9.73/3.46  #SimpNegUnit  : 470
% 9.73/3.46  #BackRed      : 1
% 9.73/3.46  
% 9.73/3.46  #Partial instantiations: 0
% 9.73/3.46  #Strategies tried      : 1
% 9.73/3.46  
% 9.73/3.46  Timing (in seconds)
% 9.73/3.46  ----------------------
% 9.73/3.46  Preprocessing        : 0.34
% 9.73/3.46  Parsing              : 0.19
% 9.73/3.46  CNF conversion       : 0.03
% 9.73/3.46  Main loop            : 2.32
% 9.73/3.46  Inferencing          : 0.57
% 9.73/3.46  Reduction            : 1.05
% 9.73/3.46  Demodulation         : 0.87
% 9.73/3.46  BG Simplification    : 0.07
% 9.73/3.46  Subsumption          : 0.50
% 9.73/3.46  Abstraction          : 0.11
% 9.73/3.46  MUC search           : 0.00
% 9.73/3.46  Cooper               : 0.00
% 9.73/3.46  Total                : 2.68
% 9.73/3.46  Index Insertion      : 0.00
% 9.73/3.46  Index Deletion       : 0.00
% 9.73/3.46  Index Matching       : 0.00
% 9.73/3.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
