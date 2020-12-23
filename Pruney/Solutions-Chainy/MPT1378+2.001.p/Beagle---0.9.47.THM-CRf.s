%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:03 EST 2020

% Result     : Theorem 10.08s
% Output     : CNFRefutation 10.26s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 205 expanded)
%              Number of leaves         :   34 (  87 expanded)
%              Depth                    :   14
%              Number of atoms          :  204 ( 712 expanded)
%              Number of equality atoms :   14 (  25 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k4_subset_1 > k2_xboole_0 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_132,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_connsp_2)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_95,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_31,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_32,plain,(
    m1_connsp_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(A_1,k2_xboole_0(A_1,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_238,plain,(
    ! [A_93,B_94,C_95] :
      ( k4_subset_1(A_93,B_94,C_95) = k2_xboole_0(B_94,C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(A_93))
      | ~ m1_subset_1(B_94,k1_zfmisc_1(A_93)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_261,plain,(
    ! [B_99] :
      ( k4_subset_1(u1_struct_0('#skF_1'),B_99,'#skF_3') = k2_xboole_0(B_99,'#skF_3')
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_38,c_238])).

tff(c_274,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_4','#skF_3') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_261])).

tff(c_283,plain,(
    ! [A_100,B_101,C_102] :
      ( m1_subset_1(k4_subset_1(A_100,B_101,C_102),k1_zfmisc_1(A_100))
      | ~ m1_subset_1(C_102,k1_zfmisc_1(A_100))
      | ~ m1_subset_1(B_101,k1_zfmisc_1(A_100)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_299,plain,
    ( m1_subset_1(k2_xboole_0('#skF_4','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_283])).

tff(c_310,plain,(
    m1_subset_1(k2_xboole_0('#skF_4','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_38,c_299])).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_22,plain,(
    ! [A_23,B_27,C_29] :
      ( r1_tarski(k1_tops_1(A_23,B_27),k1_tops_1(A_23,C_29))
      | ~ r1_tarski(B_27,C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_44,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_763,plain,(
    ! [B_128,A_129,C_130] :
      ( r2_hidden(B_128,k1_tops_1(A_129,C_130))
      | ~ m1_connsp_2(C_130,A_129,B_128)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ m1_subset_1(B_128,u1_struct_0(A_129))
      | ~ l1_pre_topc(A_129)
      | ~ v2_pre_topc(A_129)
      | v2_struct_0(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_787,plain,(
    ! [B_128] :
      ( r2_hidden(B_128,k1_tops_1('#skF_1','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_1',B_128)
      | ~ m1_subset_1(B_128,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_36,c_763])).

tff(c_824,plain,(
    ! [B_128] :
      ( r2_hidden(B_128,k1_tops_1('#skF_1','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_1',B_128)
      | ~ m1_subset_1(B_128,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_787])).

tff(c_959,plain,(
    ! [B_134] :
      ( r2_hidden(B_134,k1_tops_1('#skF_1','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_1',B_134)
      | ~ m1_subset_1(B_134,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_824])).

tff(c_16,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,k1_zfmisc_1(B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_184,plain,(
    ! [C_70,B_71,A_72] :
      ( ~ v1_xboole_0(C_70)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(C_70))
      | ~ r2_hidden(A_72,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_191,plain,(
    ! [B_16,A_72,A_15] :
      ( ~ v1_xboole_0(B_16)
      | ~ r2_hidden(A_72,A_15)
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(resolution,[status(thm)],[c_16,c_184])).

tff(c_971,plain,(
    ! [B_16,B_134] :
      ( ~ v1_xboole_0(B_16)
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_4'),B_16)
      | ~ m1_connsp_2('#skF_4','#skF_1',B_134)
      | ~ m1_subset_1(B_134,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_959,c_191])).

tff(c_1827,plain,(
    ! [B_182] :
      ( ~ m1_connsp_2('#skF_4','#skF_1',B_182)
      | ~ m1_subset_1(B_182,u1_struct_0('#skF_1')) ) ),
    inference(splitLeft,[status(thm)],[c_971])).

tff(c_1836,plain,(
    ~ m1_connsp_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_1827])).

tff(c_1842,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1836])).

tff(c_1844,plain,(
    ! [B_183] :
      ( ~ v1_xboole_0(B_183)
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_4'),B_183) ) ),
    inference(splitRight,[status(thm)],[c_971])).

tff(c_1848,plain,(
    ! [C_29] :
      ( ~ v1_xboole_0(k1_tops_1('#skF_1',C_29))
      | ~ r1_tarski('#skF_4',C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_22,c_1844])).

tff(c_1933,plain,(
    ! [C_191] :
      ( ~ v1_xboole_0(k1_tops_1('#skF_1',C_191))
      | ~ r1_tarski('#skF_4',C_191)
      | ~ m1_subset_1(C_191,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_36,c_1848])).

tff(c_1960,plain,
    ( ~ v1_xboole_0(k1_tops_1('#skF_1',k2_xboole_0('#skF_4','#skF_3')))
    | ~ r1_tarski('#skF_4',k2_xboole_0('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_310,c_1933])).

tff(c_1993,plain,(
    ~ v1_xboole_0(k1_tops_1('#skF_1',k2_xboole_0('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1960])).

tff(c_14,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | ~ m1_subset_1(A_15,k1_zfmisc_1(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_330,plain,(
    r1_tarski(k2_xboole_0('#skF_4','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_310,c_14])).

tff(c_195,plain,(
    ! [A_73,C_74,B_75] :
      ( m1_subset_1(A_73,C_74)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(C_74))
      | ~ r2_hidden(A_73,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_202,plain,(
    ! [A_73,B_16,A_15] :
      ( m1_subset_1(A_73,B_16)
      | ~ r2_hidden(A_73,A_15)
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(resolution,[status(thm)],[c_16,c_195])).

tff(c_2300,plain,(
    ! [B_204,B_205] :
      ( m1_subset_1(B_204,B_205)
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_4'),B_205)
      | ~ m1_connsp_2('#skF_4','#skF_1',B_204)
      | ~ m1_subset_1(B_204,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_959,c_202])).

tff(c_2303,plain,(
    ! [B_204,C_29] :
      ( m1_subset_1(B_204,k1_tops_1('#skF_1',C_29))
      | ~ m1_connsp_2('#skF_4','#skF_1',B_204)
      | ~ m1_subset_1(B_204,u1_struct_0('#skF_1'))
      | ~ r1_tarski('#skF_4',C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_22,c_2300])).

tff(c_9235,plain,(
    ! [B_353,C_354] :
      ( m1_subset_1(B_353,k1_tops_1('#skF_1',C_354))
      | ~ m1_connsp_2('#skF_4','#skF_1',B_353)
      | ~ m1_subset_1(B_353,u1_struct_0('#skF_1'))
      | ~ r1_tarski('#skF_4',C_354)
      | ~ m1_subset_1(C_354,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_36,c_2303])).

tff(c_9277,plain,(
    ! [B_353] :
      ( m1_subset_1(B_353,k1_tops_1('#skF_1',k2_xboole_0('#skF_4','#skF_3')))
      | ~ m1_connsp_2('#skF_4','#skF_1',B_353)
      | ~ m1_subset_1(B_353,u1_struct_0('#skF_1'))
      | ~ r1_tarski('#skF_4',k2_xboole_0('#skF_4','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_310,c_9235])).

tff(c_9354,plain,(
    ! [B_358] :
      ( m1_subset_1(B_358,k1_tops_1('#skF_1',k2_xboole_0('#skF_4','#skF_3')))
      | ~ m1_connsp_2('#skF_4','#skF_1',B_358)
      | ~ m1_subset_1(B_358,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_9277])).

tff(c_12,plain,(
    ! [A_13,B_14] :
      ( r2_hidden(A_13,B_14)
      | v1_xboole_0(B_14)
      | ~ m1_subset_1(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_644,plain,(
    ! [C_122,A_123,B_124] :
      ( m1_connsp_2(C_122,A_123,B_124)
      | ~ r2_hidden(B_124,k1_tops_1(A_123,C_122))
      | ~ m1_subset_1(C_122,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ m1_subset_1(B_124,u1_struct_0(A_123))
      | ~ l1_pre_topc(A_123)
      | ~ v2_pre_topc(A_123)
      | v2_struct_0(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1999,plain,(
    ! [C_192,A_193,A_194] :
      ( m1_connsp_2(C_192,A_193,A_194)
      | ~ m1_subset_1(C_192,k1_zfmisc_1(u1_struct_0(A_193)))
      | ~ m1_subset_1(A_194,u1_struct_0(A_193))
      | ~ l1_pre_topc(A_193)
      | ~ v2_pre_topc(A_193)
      | v2_struct_0(A_193)
      | v1_xboole_0(k1_tops_1(A_193,C_192))
      | ~ m1_subset_1(A_194,k1_tops_1(A_193,C_192)) ) ),
    inference(resolution,[status(thm)],[c_12,c_644])).

tff(c_2065,plain,(
    ! [A_15,A_193,A_194] :
      ( m1_connsp_2(A_15,A_193,A_194)
      | ~ m1_subset_1(A_194,u1_struct_0(A_193))
      | ~ l1_pre_topc(A_193)
      | ~ v2_pre_topc(A_193)
      | v2_struct_0(A_193)
      | v1_xboole_0(k1_tops_1(A_193,A_15))
      | ~ m1_subset_1(A_194,k1_tops_1(A_193,A_15))
      | ~ r1_tarski(A_15,u1_struct_0(A_193)) ) ),
    inference(resolution,[status(thm)],[c_16,c_1999])).

tff(c_9356,plain,(
    ! [B_358] :
      ( m1_connsp_2(k2_xboole_0('#skF_4','#skF_3'),'#skF_1',B_358)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | v1_xboole_0(k1_tops_1('#skF_1',k2_xboole_0('#skF_4','#skF_3')))
      | ~ r1_tarski(k2_xboole_0('#skF_4','#skF_3'),u1_struct_0('#skF_1'))
      | ~ m1_connsp_2('#skF_4','#skF_1',B_358)
      | ~ m1_subset_1(B_358,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_9354,c_2065])).

tff(c_9362,plain,(
    ! [B_358] :
      ( m1_connsp_2(k2_xboole_0('#skF_4','#skF_3'),'#skF_1',B_358)
      | v2_struct_0('#skF_1')
      | v1_xboole_0(k1_tops_1('#skF_1',k2_xboole_0('#skF_4','#skF_3')))
      | ~ m1_connsp_2('#skF_4','#skF_1',B_358)
      | ~ m1_subset_1(B_358,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_330,c_44,c_42,c_9356])).

tff(c_9365,plain,(
    ! [B_359] :
      ( m1_connsp_2(k2_xboole_0('#skF_4','#skF_3'),'#skF_1',B_359)
      | ~ m1_connsp_2('#skF_4','#skF_1',B_359)
      | ~ m1_subset_1(B_359,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1993,c_46,c_9362])).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_81,plain,(
    ! [A_56,B_57] : k3_tarski(k2_tarski(A_56,B_57)) = k2_xboole_0(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_110,plain,(
    ! [A_62,B_63] : k3_tarski(k2_tarski(A_62,B_63)) = k2_xboole_0(B_63,A_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_81])).

tff(c_6,plain,(
    ! [A_5,B_6] : k3_tarski(k2_tarski(A_5,B_6)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_116,plain,(
    ! [B_63,A_62] : k2_xboole_0(B_63,A_62) = k2_xboole_0(A_62,B_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_6])).

tff(c_337,plain,(
    ! [B_103] :
      ( k4_subset_1(u1_struct_0('#skF_1'),B_103,'#skF_4') = k2_xboole_0(B_103,'#skF_4')
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_36,c_238])).

tff(c_351,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_3','#skF_4') = k2_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_337])).

tff(c_361,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_3','#skF_4') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_351])).

tff(c_30,plain,(
    ~ m1_connsp_2(k4_subset_1(u1_struct_0('#skF_1'),'#skF_3','#skF_4'),'#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_441,plain,(
    ~ m1_connsp_2(k2_xboole_0('#skF_4','#skF_3'),'#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_361,c_30])).

tff(c_9371,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_9365,c_441])).

tff(c_9378,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_32,c_9371])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.32  % Computer   : n019.cluster.edu
% 0.14/0.32  % Model      : x86_64 x86_64
% 0.14/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.32  % Memory     : 8042.1875MB
% 0.14/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.32  % CPULimit   : 60
% 0.14/0.32  % DateTime   : Tue Dec  1 15:22:37 EST 2020
% 0.14/0.32  % CPUTime    : 
% 0.14/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.08/3.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.26/3.43  
% 10.26/3.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.26/3.43  %$ m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k4_subset_1 > k2_xboole_0 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 10.26/3.43  
% 10.26/3.43  %Foreground sorts:
% 10.26/3.43  
% 10.26/3.43  
% 10.26/3.43  %Background operators:
% 10.26/3.43  
% 10.26/3.43  
% 10.26/3.43  %Foreground operators:
% 10.26/3.43  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 10.26/3.43  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 10.26/3.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.26/3.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.26/3.43  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.26/3.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.26/3.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.26/3.43  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 10.26/3.43  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 10.26/3.43  tff('#skF_2', type, '#skF_2': $i).
% 10.26/3.43  tff('#skF_3', type, '#skF_3': $i).
% 10.26/3.43  tff('#skF_1', type, '#skF_1': $i).
% 10.26/3.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.26/3.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.26/3.43  tff(k3_tarski, type, k3_tarski: $i > $i).
% 10.26/3.43  tff('#skF_4', type, '#skF_4': $i).
% 10.26/3.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.26/3.43  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 10.26/3.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.26/3.43  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.26/3.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.26/3.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.26/3.43  
% 10.26/3.45  tff(f_132, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ((m1_connsp_2(C, A, B) & m1_connsp_2(D, A, B)) => m1_connsp_2(k4_subset_1(u1_struct_0(A), C, D), A, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_connsp_2)).
% 10.26/3.45  tff(f_27, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 10.26/3.45  tff(f_43, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 10.26/3.45  tff(f_37, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 10.26/3.45  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 10.26/3.45  tff(f_95, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 10.26/3.45  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 10.26/3.45  tff(f_66, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 10.26/3.45  tff(f_59, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 10.26/3.45  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 10.26/3.45  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 10.26/3.45  tff(f_31, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 10.26/3.45  tff(c_40, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 10.26/3.45  tff(c_32, plain, (m1_connsp_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 10.26/3.45  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.26/3.45  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 10.26/3.45  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 10.26/3.45  tff(c_238, plain, (![A_93, B_94, C_95]: (k4_subset_1(A_93, B_94, C_95)=k2_xboole_0(B_94, C_95) | ~m1_subset_1(C_95, k1_zfmisc_1(A_93)) | ~m1_subset_1(B_94, k1_zfmisc_1(A_93)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.26/3.45  tff(c_261, plain, (![B_99]: (k4_subset_1(u1_struct_0('#skF_1'), B_99, '#skF_3')=k2_xboole_0(B_99, '#skF_3') | ~m1_subset_1(B_99, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_38, c_238])).
% 10.26/3.45  tff(c_274, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_4', '#skF_3')=k2_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_261])).
% 10.26/3.45  tff(c_283, plain, (![A_100, B_101, C_102]: (m1_subset_1(k4_subset_1(A_100, B_101, C_102), k1_zfmisc_1(A_100)) | ~m1_subset_1(C_102, k1_zfmisc_1(A_100)) | ~m1_subset_1(B_101, k1_zfmisc_1(A_100)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.26/3.45  tff(c_299, plain, (m1_subset_1(k2_xboole_0('#skF_4', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_274, c_283])).
% 10.26/3.45  tff(c_310, plain, (m1_subset_1(k2_xboole_0('#skF_4', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_38, c_299])).
% 10.26/3.45  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_132])).
% 10.26/3.45  tff(c_22, plain, (![A_23, B_27, C_29]: (r1_tarski(k1_tops_1(A_23, B_27), k1_tops_1(A_23, C_29)) | ~r1_tarski(B_27, C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(u1_struct_0(A_23))) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.26/3.45  tff(c_46, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_132])).
% 10.26/3.45  tff(c_44, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_132])).
% 10.26/3.45  tff(c_763, plain, (![B_128, A_129, C_130]: (r2_hidden(B_128, k1_tops_1(A_129, C_130)) | ~m1_connsp_2(C_130, A_129, B_128) | ~m1_subset_1(C_130, k1_zfmisc_1(u1_struct_0(A_129))) | ~m1_subset_1(B_128, u1_struct_0(A_129)) | ~l1_pre_topc(A_129) | ~v2_pre_topc(A_129) | v2_struct_0(A_129))), inference(cnfTransformation, [status(thm)], [f_95])).
% 10.26/3.45  tff(c_787, plain, (![B_128]: (r2_hidden(B_128, k1_tops_1('#skF_1', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_1', B_128) | ~m1_subset_1(B_128, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_763])).
% 10.26/3.45  tff(c_824, plain, (![B_128]: (r2_hidden(B_128, k1_tops_1('#skF_1', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_1', B_128) | ~m1_subset_1(B_128, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_787])).
% 10.26/3.45  tff(c_959, plain, (![B_134]: (r2_hidden(B_134, k1_tops_1('#skF_1', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_1', B_134) | ~m1_subset_1(B_134, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_46, c_824])).
% 10.26/3.45  tff(c_16, plain, (![A_15, B_16]: (m1_subset_1(A_15, k1_zfmisc_1(B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.26/3.45  tff(c_184, plain, (![C_70, B_71, A_72]: (~v1_xboole_0(C_70) | ~m1_subset_1(B_71, k1_zfmisc_1(C_70)) | ~r2_hidden(A_72, B_71))), inference(cnfTransformation, [status(thm)], [f_66])).
% 10.26/3.45  tff(c_191, plain, (![B_16, A_72, A_15]: (~v1_xboole_0(B_16) | ~r2_hidden(A_72, A_15) | ~r1_tarski(A_15, B_16))), inference(resolution, [status(thm)], [c_16, c_184])).
% 10.26/3.45  tff(c_971, plain, (![B_16, B_134]: (~v1_xboole_0(B_16) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_4'), B_16) | ~m1_connsp_2('#skF_4', '#skF_1', B_134) | ~m1_subset_1(B_134, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_959, c_191])).
% 10.26/3.45  tff(c_1827, plain, (![B_182]: (~m1_connsp_2('#skF_4', '#skF_1', B_182) | ~m1_subset_1(B_182, u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_971])).
% 10.26/3.45  tff(c_1836, plain, (~m1_connsp_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_40, c_1827])).
% 10.26/3.45  tff(c_1842, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_1836])).
% 10.26/3.45  tff(c_1844, plain, (![B_183]: (~v1_xboole_0(B_183) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_4'), B_183))), inference(splitRight, [status(thm)], [c_971])).
% 10.26/3.45  tff(c_1848, plain, (![C_29]: (~v1_xboole_0(k1_tops_1('#skF_1', C_29)) | ~r1_tarski('#skF_4', C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_22, c_1844])).
% 10.26/3.45  tff(c_1933, plain, (![C_191]: (~v1_xboole_0(k1_tops_1('#skF_1', C_191)) | ~r1_tarski('#skF_4', C_191) | ~m1_subset_1(C_191, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_36, c_1848])).
% 10.26/3.45  tff(c_1960, plain, (~v1_xboole_0(k1_tops_1('#skF_1', k2_xboole_0('#skF_4', '#skF_3'))) | ~r1_tarski('#skF_4', k2_xboole_0('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_310, c_1933])).
% 10.26/3.45  tff(c_1993, plain, (~v1_xboole_0(k1_tops_1('#skF_1', k2_xboole_0('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1960])).
% 10.26/3.45  tff(c_14, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | ~m1_subset_1(A_15, k1_zfmisc_1(B_16)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.26/3.45  tff(c_330, plain, (r1_tarski(k2_xboole_0('#skF_4', '#skF_3'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_310, c_14])).
% 10.26/3.45  tff(c_195, plain, (![A_73, C_74, B_75]: (m1_subset_1(A_73, C_74) | ~m1_subset_1(B_75, k1_zfmisc_1(C_74)) | ~r2_hidden(A_73, B_75))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.26/3.45  tff(c_202, plain, (![A_73, B_16, A_15]: (m1_subset_1(A_73, B_16) | ~r2_hidden(A_73, A_15) | ~r1_tarski(A_15, B_16))), inference(resolution, [status(thm)], [c_16, c_195])).
% 10.26/3.45  tff(c_2300, plain, (![B_204, B_205]: (m1_subset_1(B_204, B_205) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_4'), B_205) | ~m1_connsp_2('#skF_4', '#skF_1', B_204) | ~m1_subset_1(B_204, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_959, c_202])).
% 10.26/3.45  tff(c_2303, plain, (![B_204, C_29]: (m1_subset_1(B_204, k1_tops_1('#skF_1', C_29)) | ~m1_connsp_2('#skF_4', '#skF_1', B_204) | ~m1_subset_1(B_204, u1_struct_0('#skF_1')) | ~r1_tarski('#skF_4', C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_22, c_2300])).
% 10.26/3.45  tff(c_9235, plain, (![B_353, C_354]: (m1_subset_1(B_353, k1_tops_1('#skF_1', C_354)) | ~m1_connsp_2('#skF_4', '#skF_1', B_353) | ~m1_subset_1(B_353, u1_struct_0('#skF_1')) | ~r1_tarski('#skF_4', C_354) | ~m1_subset_1(C_354, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_36, c_2303])).
% 10.26/3.45  tff(c_9277, plain, (![B_353]: (m1_subset_1(B_353, k1_tops_1('#skF_1', k2_xboole_0('#skF_4', '#skF_3'))) | ~m1_connsp_2('#skF_4', '#skF_1', B_353) | ~m1_subset_1(B_353, u1_struct_0('#skF_1')) | ~r1_tarski('#skF_4', k2_xboole_0('#skF_4', '#skF_3')))), inference(resolution, [status(thm)], [c_310, c_9235])).
% 10.26/3.45  tff(c_9354, plain, (![B_358]: (m1_subset_1(B_358, k1_tops_1('#skF_1', k2_xboole_0('#skF_4', '#skF_3'))) | ~m1_connsp_2('#skF_4', '#skF_1', B_358) | ~m1_subset_1(B_358, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_9277])).
% 10.26/3.45  tff(c_12, plain, (![A_13, B_14]: (r2_hidden(A_13, B_14) | v1_xboole_0(B_14) | ~m1_subset_1(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.26/3.45  tff(c_644, plain, (![C_122, A_123, B_124]: (m1_connsp_2(C_122, A_123, B_124) | ~r2_hidden(B_124, k1_tops_1(A_123, C_122)) | ~m1_subset_1(C_122, k1_zfmisc_1(u1_struct_0(A_123))) | ~m1_subset_1(B_124, u1_struct_0(A_123)) | ~l1_pre_topc(A_123) | ~v2_pre_topc(A_123) | v2_struct_0(A_123))), inference(cnfTransformation, [status(thm)], [f_95])).
% 10.26/3.45  tff(c_1999, plain, (![C_192, A_193, A_194]: (m1_connsp_2(C_192, A_193, A_194) | ~m1_subset_1(C_192, k1_zfmisc_1(u1_struct_0(A_193))) | ~m1_subset_1(A_194, u1_struct_0(A_193)) | ~l1_pre_topc(A_193) | ~v2_pre_topc(A_193) | v2_struct_0(A_193) | v1_xboole_0(k1_tops_1(A_193, C_192)) | ~m1_subset_1(A_194, k1_tops_1(A_193, C_192)))), inference(resolution, [status(thm)], [c_12, c_644])).
% 10.26/3.45  tff(c_2065, plain, (![A_15, A_193, A_194]: (m1_connsp_2(A_15, A_193, A_194) | ~m1_subset_1(A_194, u1_struct_0(A_193)) | ~l1_pre_topc(A_193) | ~v2_pre_topc(A_193) | v2_struct_0(A_193) | v1_xboole_0(k1_tops_1(A_193, A_15)) | ~m1_subset_1(A_194, k1_tops_1(A_193, A_15)) | ~r1_tarski(A_15, u1_struct_0(A_193)))), inference(resolution, [status(thm)], [c_16, c_1999])).
% 10.26/3.45  tff(c_9356, plain, (![B_358]: (m1_connsp_2(k2_xboole_0('#skF_4', '#skF_3'), '#skF_1', B_358) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | v1_xboole_0(k1_tops_1('#skF_1', k2_xboole_0('#skF_4', '#skF_3'))) | ~r1_tarski(k2_xboole_0('#skF_4', '#skF_3'), u1_struct_0('#skF_1')) | ~m1_connsp_2('#skF_4', '#skF_1', B_358) | ~m1_subset_1(B_358, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_9354, c_2065])).
% 10.26/3.45  tff(c_9362, plain, (![B_358]: (m1_connsp_2(k2_xboole_0('#skF_4', '#skF_3'), '#skF_1', B_358) | v2_struct_0('#skF_1') | v1_xboole_0(k1_tops_1('#skF_1', k2_xboole_0('#skF_4', '#skF_3'))) | ~m1_connsp_2('#skF_4', '#skF_1', B_358) | ~m1_subset_1(B_358, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_330, c_44, c_42, c_9356])).
% 10.26/3.45  tff(c_9365, plain, (![B_359]: (m1_connsp_2(k2_xboole_0('#skF_4', '#skF_3'), '#skF_1', B_359) | ~m1_connsp_2('#skF_4', '#skF_1', B_359) | ~m1_subset_1(B_359, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_1993, c_46, c_9362])).
% 10.26/3.45  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.26/3.45  tff(c_81, plain, (![A_56, B_57]: (k3_tarski(k2_tarski(A_56, B_57))=k2_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.26/3.45  tff(c_110, plain, (![A_62, B_63]: (k3_tarski(k2_tarski(A_62, B_63))=k2_xboole_0(B_63, A_62))), inference(superposition, [status(thm), theory('equality')], [c_4, c_81])).
% 10.26/3.45  tff(c_6, plain, (![A_5, B_6]: (k3_tarski(k2_tarski(A_5, B_6))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.26/3.45  tff(c_116, plain, (![B_63, A_62]: (k2_xboole_0(B_63, A_62)=k2_xboole_0(A_62, B_63))), inference(superposition, [status(thm), theory('equality')], [c_110, c_6])).
% 10.26/3.45  tff(c_337, plain, (![B_103]: (k4_subset_1(u1_struct_0('#skF_1'), B_103, '#skF_4')=k2_xboole_0(B_103, '#skF_4') | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_36, c_238])).
% 10.26/3.45  tff(c_351, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_3', '#skF_4')=k2_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_38, c_337])).
% 10.26/3.45  tff(c_361, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_3', '#skF_4')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_116, c_351])).
% 10.26/3.45  tff(c_30, plain, (~m1_connsp_2(k4_subset_1(u1_struct_0('#skF_1'), '#skF_3', '#skF_4'), '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 10.26/3.45  tff(c_441, plain, (~m1_connsp_2(k2_xboole_0('#skF_4', '#skF_3'), '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_361, c_30])).
% 10.26/3.45  tff(c_9371, plain, (~m1_connsp_2('#skF_4', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_9365, c_441])).
% 10.26/3.45  tff(c_9378, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_32, c_9371])).
% 10.26/3.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.26/3.45  
% 10.26/3.45  Inference rules
% 10.26/3.45  ----------------------
% 10.26/3.45  #Ref     : 0
% 10.26/3.45  #Sup     : 2090
% 10.26/3.45  #Fact    : 0
% 10.26/3.45  #Define  : 0
% 10.26/3.45  #Split   : 21
% 10.26/3.45  #Chain   : 0
% 10.26/3.45  #Close   : 0
% 10.26/3.45  
% 10.26/3.45  Ordering : KBO
% 10.26/3.45  
% 10.26/3.45  Simplification rules
% 10.26/3.45  ----------------------
% 10.26/3.45  #Subsume      : 472
% 10.26/3.45  #Demod        : 2873
% 10.26/3.45  #Tautology    : 378
% 10.26/3.45  #SimpNegUnit  : 272
% 10.26/3.45  #BackRed      : 1
% 10.26/3.45  
% 10.26/3.45  #Partial instantiations: 0
% 10.26/3.45  #Strategies tried      : 1
% 10.26/3.45  
% 10.26/3.45  Timing (in seconds)
% 10.26/3.45  ----------------------
% 10.26/3.45  Preprocessing        : 0.34
% 10.26/3.45  Parsing              : 0.18
% 10.26/3.45  CNF conversion       : 0.02
% 10.26/3.45  Main loop            : 2.36
% 10.26/3.45  Inferencing          : 0.56
% 10.26/3.45  Reduction            : 1.12
% 10.26/3.45  Demodulation         : 0.92
% 10.26/3.45  BG Simplification    : 0.06
% 10.26/3.45  Subsumption          : 0.48
% 10.26/3.45  Abstraction          : 0.10
% 10.26/3.45  MUC search           : 0.00
% 10.26/3.45  Cooper               : 0.00
% 10.26/3.45  Total                : 2.74
% 10.26/3.45  Index Insertion      : 0.00
% 10.26/3.45  Index Deletion       : 0.00
% 10.26/3.45  Index Matching       : 0.00
% 10.26/3.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
