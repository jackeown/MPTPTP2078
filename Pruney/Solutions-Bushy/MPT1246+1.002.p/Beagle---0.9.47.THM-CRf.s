%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1246+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:38 EST 2020

% Result     : Theorem 26.09s
% Output     : CNFRefutation 26.09s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 956 expanded)
%              Number of leaves         :   33 ( 349 expanded)
%              Depth                    :   23
%              Number of atoms          :  478 (4520 expanded)
%              Number of equality atoms :   33 ( 153 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_114,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( r2_hidden(C,k2_tops_1(A,B))
                <=> ! [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                     => ( ( v3_pre_topc(D,A)
                          & r2_hidden(C,D) )
                       => ( ~ r1_xboole_0(B,D)
                          & ~ r1_xboole_0(k3_subset_1(u1_struct_0(A),B),D) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_tops_1)).

tff(f_85,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_hidden(C,k2_pre_topc(A,B))
              <=> ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                   => ~ ( v3_pre_topc(D,A)
                        & r2_hidden(C,D)
                        & r1_xboole_0(B,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_tops_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_26,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_30,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_37,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_42,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_54,plain,
    ( r2_hidden('#skF_6','#skF_7')
    | ~ r2_hidden('#skF_6',k2_tops_1('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_114,plain,(
    ~ r2_hidden('#skF_6',k2_tops_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_48,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_46,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_59736,plain,(
    ! [B_3012,A_3013,C_3014] :
      ( r1_xboole_0(B_3012,'#skF_3'(A_3013,B_3012,C_3014))
      | r2_hidden(C_3014,k2_pre_topc(A_3013,B_3012))
      | ~ m1_subset_1(C_3014,u1_struct_0(A_3013))
      | ~ m1_subset_1(B_3012,k1_zfmisc_1(u1_struct_0(A_3013)))
      | ~ l1_pre_topc(A_3013)
      | ~ v2_pre_topc(A_3013)
      | v2_struct_0(A_3013) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_59745,plain,(
    ! [C_3014] :
      ( r1_xboole_0('#skF_5','#skF_3'('#skF_4','#skF_5',C_3014))
      | r2_hidden(C_3014,k2_pre_topc('#skF_4','#skF_5'))
      | ~ m1_subset_1(C_3014,u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_59736])).

tff(c_59754,plain,(
    ! [C_3014] :
      ( r1_xboole_0('#skF_5','#skF_3'('#skF_4','#skF_5',C_3014))
      | r2_hidden(C_3014,k2_pre_topc('#skF_4','#skF_5'))
      | ~ m1_subset_1(C_3014,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_59745])).

tff(c_59755,plain,(
    ! [C_3014] :
      ( r1_xboole_0('#skF_5','#skF_3'('#skF_4','#skF_5',C_3014))
      | r2_hidden(C_3014,k2_pre_topc('#skF_4','#skF_5'))
      | ~ m1_subset_1(C_3014,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_59754])).

tff(c_28,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(k3_subset_1(A_17,B_18),k1_zfmisc_1(A_17))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_60396,plain,(
    ! [C_3023,A_3024,B_3025] :
      ( r2_hidden(C_3023,'#skF_3'(A_3024,B_3025,C_3023))
      | r2_hidden(C_3023,k2_pre_topc(A_3024,B_3025))
      | ~ m1_subset_1(C_3023,u1_struct_0(A_3024))
      | ~ m1_subset_1(B_3025,k1_zfmisc_1(u1_struct_0(A_3024)))
      | ~ l1_pre_topc(A_3024)
      | ~ v2_pre_topc(A_3024)
      | v2_struct_0(A_3024) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_64267,plain,(
    ! [C_3194,A_3195,B_3196] :
      ( r2_hidden(C_3194,'#skF_3'(A_3195,k3_subset_1(u1_struct_0(A_3195),B_3196),C_3194))
      | r2_hidden(C_3194,k2_pre_topc(A_3195,k3_subset_1(u1_struct_0(A_3195),B_3196)))
      | ~ m1_subset_1(C_3194,u1_struct_0(A_3195))
      | ~ l1_pre_topc(A_3195)
      | ~ v2_pre_topc(A_3195)
      | v2_struct_0(A_3195)
      | ~ m1_subset_1(B_3196,k1_zfmisc_1(u1_struct_0(A_3195))) ) ),
    inference(resolution,[status(thm)],[c_28,c_60396])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_186,plain,(
    ! [A_84,B_85] :
      ( m1_subset_1(k2_pre_topc(A_84,B_85),k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_pre_topc(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_30,plain,(
    ! [A_19,B_20,C_21] :
      ( k9_subset_1(A_19,B_20,C_21) = k3_xboole_0(B_20,C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_59460,plain,(
    ! [A_3001,B_3002,B_3003] :
      ( k9_subset_1(u1_struct_0(A_3001),B_3002,k2_pre_topc(A_3001,B_3003)) = k3_xboole_0(B_3002,k2_pre_topc(A_3001,B_3003))
      | ~ m1_subset_1(B_3003,k1_zfmisc_1(u1_struct_0(A_3001)))
      | ~ l1_pre_topc(A_3001) ) ),
    inference(resolution,[status(thm)],[c_186,c_30])).

tff(c_59469,plain,(
    ! [B_3002] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_3002,k2_pre_topc('#skF_4','#skF_5')) = k3_xboole_0(B_3002,k2_pre_topc('#skF_4','#skF_5'))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_59460])).

tff(c_59477,plain,(
    ! [B_3002] : k9_subset_1(u1_struct_0('#skF_4'),B_3002,k2_pre_topc('#skF_4','#skF_5')) = k3_xboole_0(B_3002,k2_pre_topc('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_59469])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( k9_subset_1(A_3,C_5,B_4) = k9_subset_1(A_3,B_4,C_5)
      | ~ m1_subset_1(C_5,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_59792,plain,(
    ! [A_3017,B_3018,B_3019] :
      ( k9_subset_1(u1_struct_0(A_3017),k2_pre_topc(A_3017,B_3018),B_3019) = k9_subset_1(u1_struct_0(A_3017),B_3019,k2_pre_topc(A_3017,B_3018))
      | ~ m1_subset_1(B_3018,k1_zfmisc_1(u1_struct_0(A_3017)))
      | ~ l1_pre_topc(A_3017) ) ),
    inference(resolution,[status(thm)],[c_186,c_4])).

tff(c_59801,plain,(
    ! [B_3019] :
      ( k9_subset_1(u1_struct_0('#skF_4'),k2_pre_topc('#skF_4','#skF_5'),B_3019) = k9_subset_1(u1_struct_0('#skF_4'),B_3019,k2_pre_topc('#skF_4','#skF_5'))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_59792])).

tff(c_59810,plain,(
    ! [B_3020] : k9_subset_1(u1_struct_0('#skF_4'),k2_pre_topc('#skF_4','#skF_5'),B_3020) = k3_xboole_0(B_3020,k2_pre_topc('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_59477,c_59801])).

tff(c_6,plain,(
    ! [A_6,B_8] :
      ( k9_subset_1(u1_struct_0(A_6),k2_pre_topc(A_6,B_8),k2_pre_topc(A_6,k3_subset_1(u1_struct_0(A_6),B_8))) = k2_tops_1(A_6,B_8)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_59829,plain,
    ( k3_xboole_0(k2_pre_topc('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')),k2_pre_topc('#skF_4','#skF_5')) = k2_tops_1('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_59810,c_6])).

tff(c_59886,plain,(
    k3_xboole_0(k2_pre_topc('#skF_4','#skF_5'),k2_pre_topc('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'))) = k2_tops_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_2,c_59829])).

tff(c_8,plain,(
    ! [D_14,A_9,B_10] :
      ( r2_hidden(D_14,k3_xboole_0(A_9,B_10))
      | ~ r2_hidden(D_14,B_10)
      | ~ r2_hidden(D_14,A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_60091,plain,(
    ! [D_14] :
      ( r2_hidden(D_14,k2_tops_1('#skF_4','#skF_5'))
      | ~ r2_hidden(D_14,k2_pre_topc('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')))
      | ~ r2_hidden(D_14,k2_pre_topc('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59886,c_8])).

tff(c_64277,plain,(
    ! [C_3194] :
      ( r2_hidden(C_3194,k2_tops_1('#skF_4','#skF_5'))
      | ~ r2_hidden(C_3194,k2_pre_topc('#skF_4','#skF_5'))
      | r2_hidden(C_3194,'#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),C_3194))
      | ~ m1_subset_1(C_3194,u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_64267,c_60091])).

tff(c_64289,plain,(
    ! [C_3194] :
      ( r2_hidden(C_3194,k2_tops_1('#skF_4','#skF_5'))
      | ~ r2_hidden(C_3194,k2_pre_topc('#skF_4','#skF_5'))
      | r2_hidden(C_3194,'#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),C_3194))
      | ~ m1_subset_1(C_3194,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_48,c_46,c_64277])).

tff(c_64290,plain,(
    ! [C_3194] :
      ( r2_hidden(C_3194,k2_tops_1('#skF_4','#skF_5'))
      | ~ r2_hidden(C_3194,k2_pre_topc('#skF_4','#skF_5'))
      | r2_hidden(C_3194,'#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),C_3194))
      | ~ m1_subset_1(C_3194,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_64289])).

tff(c_59437,plain,(
    ! [A_2995,B_2996,C_2997] :
      ( v3_pre_topc('#skF_3'(A_2995,B_2996,C_2997),A_2995)
      | r2_hidden(C_2997,k2_pre_topc(A_2995,B_2996))
      | ~ m1_subset_1(C_2997,u1_struct_0(A_2995))
      | ~ m1_subset_1(B_2996,k1_zfmisc_1(u1_struct_0(A_2995)))
      | ~ l1_pre_topc(A_2995)
      | ~ v2_pre_topc(A_2995)
      | v2_struct_0(A_2995) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_59452,plain,(
    ! [A_2995,B_18,C_2997] :
      ( v3_pre_topc('#skF_3'(A_2995,k3_subset_1(u1_struct_0(A_2995),B_18),C_2997),A_2995)
      | r2_hidden(C_2997,k2_pre_topc(A_2995,k3_subset_1(u1_struct_0(A_2995),B_18)))
      | ~ m1_subset_1(C_2997,u1_struct_0(A_2995))
      | ~ l1_pre_topc(A_2995)
      | ~ v2_pre_topc(A_2995)
      | v2_struct_0(A_2995)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_2995))) ) ),
    inference(resolution,[status(thm)],[c_28,c_59437])).

tff(c_40,plain,(
    ! [A_22,B_34,C_40] :
      ( m1_subset_1('#skF_3'(A_22,B_34,C_40),k1_zfmisc_1(u1_struct_0(A_22)))
      | r2_hidden(C_40,k2_pre_topc(A_22,B_34))
      | ~ m1_subset_1(C_40,u1_struct_0(A_22))
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ l1_pre_topc(A_22)
      | ~ v2_pre_topc(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_65852,plain,(
    ! [A_3269,B_3270,C_3271] :
      ( r1_xboole_0(k3_subset_1(u1_struct_0(A_3269),B_3270),'#skF_3'(A_3269,k3_subset_1(u1_struct_0(A_3269),B_3270),C_3271))
      | r2_hidden(C_3271,k2_pre_topc(A_3269,k3_subset_1(u1_struct_0(A_3269),B_3270)))
      | ~ m1_subset_1(C_3271,u1_struct_0(A_3269))
      | ~ l1_pre_topc(A_3269)
      | ~ v2_pre_topc(A_3269)
      | v2_struct_0(A_3269)
      | ~ m1_subset_1(B_3270,k1_zfmisc_1(u1_struct_0(A_3269))) ) ),
    inference(resolution,[status(thm)],[c_28,c_59736])).

tff(c_70,plain,(
    ! [D_62] :
      ( r2_hidden('#skF_6',k2_tops_1('#skF_4','#skF_5'))
      | ~ r1_xboole_0(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),D_62)
      | ~ r2_hidden('#skF_6',D_62)
      | ~ v3_pre_topc(D_62,'#skF_4')
      | ~ m1_subset_1(D_62,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_58803,plain,(
    ! [D_62] :
      ( ~ r1_xboole_0(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),D_62)
      | ~ r2_hidden('#skF_6',D_62)
      | ~ v3_pre_topc(D_62,'#skF_4')
      | ~ m1_subset_1(D_62,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_70])).

tff(c_65858,plain,(
    ! [C_3271] :
      ( ~ r2_hidden('#skF_6','#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),C_3271))
      | ~ v3_pre_topc('#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),C_3271),'#skF_4')
      | ~ m1_subset_1('#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),C_3271),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | r2_hidden(C_3271,k2_pre_topc('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')))
      | ~ m1_subset_1(C_3271,u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_65852,c_58803])).

tff(c_65862,plain,(
    ! [C_3271] :
      ( ~ r2_hidden('#skF_6','#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),C_3271))
      | ~ v3_pre_topc('#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),C_3271),'#skF_4')
      | ~ m1_subset_1('#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),C_3271),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | r2_hidden(C_3271,k2_pre_topc('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')))
      | ~ m1_subset_1(C_3271,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_48,c_46,c_65858])).

tff(c_67781,plain,(
    ! [C_3328] :
      ( ~ r2_hidden('#skF_6','#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),C_3328))
      | ~ v3_pre_topc('#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),C_3328),'#skF_4')
      | ~ m1_subset_1('#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),C_3328),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | r2_hidden(C_3328,k2_pre_topc('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')))
      | ~ m1_subset_1(C_3328,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_65862])).

tff(c_67785,plain,(
    ! [C_40] :
      ( ~ r2_hidden('#skF_6','#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),C_40))
      | ~ v3_pre_topc('#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),C_40),'#skF_4')
      | r2_hidden(C_40,k2_pre_topc('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')))
      | ~ m1_subset_1(C_40,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40,c_67781])).

tff(c_67788,plain,(
    ! [C_40] :
      ( ~ r2_hidden('#skF_6','#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),C_40))
      | ~ v3_pre_topc('#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),C_40),'#skF_4')
      | r2_hidden(C_40,k2_pre_topc('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')))
      | ~ m1_subset_1(C_40,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_67785])).

tff(c_67789,plain,(
    ! [C_40] :
      ( ~ r2_hidden('#skF_6','#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),C_40))
      | ~ v3_pre_topc('#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),C_40),'#skF_4')
      | r2_hidden(C_40,k2_pre_topc('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')))
      | ~ m1_subset_1(C_40,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_67788])).

tff(c_68594,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_67789])).

tff(c_68597,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_28,c_68594])).

tff(c_68601,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_68597])).

tff(c_72370,plain,(
    ! [C_3452] :
      ( ~ r2_hidden('#skF_6','#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),C_3452))
      | ~ v3_pre_topc('#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),C_3452),'#skF_4')
      | r2_hidden(C_3452,k2_pre_topc('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')))
      | ~ m1_subset_1(C_3452,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_67789])).

tff(c_72377,plain,(
    ! [C_2997] :
      ( ~ r2_hidden('#skF_6','#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),C_2997))
      | r2_hidden(C_2997,k2_pre_topc('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')))
      | ~ m1_subset_1(C_2997,u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_59452,c_72370])).

tff(c_72381,plain,(
    ! [C_2997] :
      ( ~ r2_hidden('#skF_6','#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),C_2997))
      | r2_hidden(C_2997,k2_pre_topc('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')))
      | ~ m1_subset_1(C_2997,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_48,c_46,c_72377])).

tff(c_72383,plain,(
    ! [C_3453] :
      ( ~ r2_hidden('#skF_6','#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),C_3453))
      | r2_hidden(C_3453,k2_pre_topc('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')))
      | ~ m1_subset_1(C_3453,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_72381])).

tff(c_72387,plain,
    ( r2_hidden('#skF_6',k2_pre_topc('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')))
    | r2_hidden('#skF_6',k2_tops_1('#skF_4','#skF_5'))
    | ~ r2_hidden('#skF_6',k2_pre_topc('#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_64290,c_72383])).

tff(c_72391,plain,
    ( r2_hidden('#skF_6',k2_pre_topc('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')))
    | r2_hidden('#skF_6',k2_tops_1('#skF_4','#skF_5'))
    | ~ r2_hidden('#skF_6',k2_pre_topc('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_72387])).

tff(c_72392,plain,
    ( r2_hidden('#skF_6',k2_pre_topc('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')))
    | ~ r2_hidden('#skF_6',k2_pre_topc('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_72391])).

tff(c_72393,plain,(
    ~ r2_hidden('#skF_6',k2_pre_topc('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_72392])).

tff(c_72399,plain,
    ( r1_xboole_0('#skF_5','#skF_3'('#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_59755,c_72393])).

tff(c_72405,plain,(
    r1_xboole_0('#skF_5','#skF_3'('#skF_4','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_72399])).

tff(c_60405,plain,(
    ! [C_3023] :
      ( r2_hidden(C_3023,'#skF_3'('#skF_4','#skF_5',C_3023))
      | r2_hidden(C_3023,k2_pre_topc('#skF_4','#skF_5'))
      | ~ m1_subset_1(C_3023,u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_60396])).

tff(c_60414,plain,(
    ! [C_3023] :
      ( r2_hidden(C_3023,'#skF_3'('#skF_4','#skF_5',C_3023))
      | r2_hidden(C_3023,k2_pre_topc('#skF_4','#skF_5'))
      | ~ m1_subset_1(C_3023,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_60405])).

tff(c_60415,plain,(
    ! [C_3023] :
      ( r2_hidden(C_3023,'#skF_3'('#skF_4','#skF_5',C_3023))
      | r2_hidden(C_3023,k2_pre_topc('#skF_4','#skF_5'))
      | ~ m1_subset_1(C_3023,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_60414])).

tff(c_72396,plain,
    ( r2_hidden('#skF_6','#skF_3'('#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_60415,c_72393])).

tff(c_72402,plain,(
    r2_hidden('#skF_6','#skF_3'('#skF_4','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_72396])).

tff(c_59446,plain,(
    ! [C_2997] :
      ( v3_pre_topc('#skF_3'('#skF_4','#skF_5',C_2997),'#skF_4')
      | r2_hidden(C_2997,k2_pre_topc('#skF_4','#skF_5'))
      | ~ m1_subset_1(C_2997,u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_59437])).

tff(c_59455,plain,(
    ! [C_2997] :
      ( v3_pre_topc('#skF_3'('#skF_4','#skF_5',C_2997),'#skF_4')
      | r2_hidden(C_2997,k2_pre_topc('#skF_4','#skF_5'))
      | ~ m1_subset_1(C_2997,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_59446])).

tff(c_59456,plain,(
    ! [C_2997] :
      ( v3_pre_topc('#skF_3'('#skF_4','#skF_5',C_2997),'#skF_4')
      | r2_hidden(C_2997,k2_pre_topc('#skF_4','#skF_5'))
      | ~ m1_subset_1(C_2997,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_59455])).

tff(c_60842,plain,(
    ! [A_3034,B_3035,C_3036] :
      ( m1_subset_1('#skF_3'(A_3034,B_3035,C_3036),k1_zfmisc_1(u1_struct_0(A_3034)))
      | r2_hidden(C_3036,k2_pre_topc(A_3034,B_3035))
      | ~ m1_subset_1(C_3036,u1_struct_0(A_3034))
      | ~ m1_subset_1(B_3035,k1_zfmisc_1(u1_struct_0(A_3034)))
      | ~ l1_pre_topc(A_3034)
      | ~ v2_pre_topc(A_3034)
      | v2_struct_0(A_3034) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_80,plain,(
    ! [D_62] :
      ( r2_hidden('#skF_6',k2_tops_1('#skF_4','#skF_5'))
      | ~ r1_xboole_0('#skF_5',D_62)
      | ~ r2_hidden('#skF_6',D_62)
      | ~ v3_pre_topc(D_62,'#skF_4')
      | ~ m1_subset_1(D_62,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_48823,plain,(
    ! [D_62] :
      ( ~ r1_xboole_0('#skF_5',D_62)
      | ~ r2_hidden('#skF_6',D_62)
      | ~ v3_pre_topc(D_62,'#skF_4')
      | ~ m1_subset_1(D_62,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_80])).

tff(c_60860,plain,(
    ! [B_3035,C_3036] :
      ( ~ r1_xboole_0('#skF_5','#skF_3'('#skF_4',B_3035,C_3036))
      | ~ r2_hidden('#skF_6','#skF_3'('#skF_4',B_3035,C_3036))
      | ~ v3_pre_topc('#skF_3'('#skF_4',B_3035,C_3036),'#skF_4')
      | r2_hidden(C_3036,k2_pre_topc('#skF_4',B_3035))
      | ~ m1_subset_1(C_3036,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_3035,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_60842,c_48823])).

tff(c_60880,plain,(
    ! [B_3035,C_3036] :
      ( ~ r1_xboole_0('#skF_5','#skF_3'('#skF_4',B_3035,C_3036))
      | ~ r2_hidden('#skF_6','#skF_3'('#skF_4',B_3035,C_3036))
      | ~ v3_pre_topc('#skF_3'('#skF_4',B_3035,C_3036),'#skF_4')
      | r2_hidden(C_3036,k2_pre_topc('#skF_4',B_3035))
      | ~ m1_subset_1(C_3036,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_3035,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_60860])).

tff(c_60891,plain,(
    ! [B_3038,C_3039] :
      ( ~ r1_xboole_0('#skF_5','#skF_3'('#skF_4',B_3038,C_3039))
      | ~ r2_hidden('#skF_6','#skF_3'('#skF_4',B_3038,C_3039))
      | ~ v3_pre_topc('#skF_3'('#skF_4',B_3038,C_3039),'#skF_4')
      | r2_hidden(C_3039,k2_pre_topc('#skF_4',B_3038))
      | ~ m1_subset_1(C_3039,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_3038,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_60880])).

tff(c_60895,plain,(
    ! [C_2997] :
      ( ~ r1_xboole_0('#skF_5','#skF_3'('#skF_4','#skF_5',C_2997))
      | ~ r2_hidden('#skF_6','#skF_3'('#skF_4','#skF_5',C_2997))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | r2_hidden(C_2997,k2_pre_topc('#skF_4','#skF_5'))
      | ~ m1_subset_1(C_2997,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_59456,c_60891])).

tff(c_60901,plain,(
    ! [C_2997] :
      ( ~ r1_xboole_0('#skF_5','#skF_3'('#skF_4','#skF_5',C_2997))
      | ~ r2_hidden('#skF_6','#skF_3'('#skF_4','#skF_5',C_2997))
      | r2_hidden(C_2997,k2_pre_topc('#skF_4','#skF_5'))
      | ~ m1_subset_1(C_2997,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_60895])).

tff(c_72407,plain,
    ( ~ r1_xboole_0('#skF_5','#skF_3'('#skF_4','#skF_5','#skF_6'))
    | r2_hidden('#skF_6',k2_pre_topc('#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_72402,c_60901])).

tff(c_72410,plain,
    ( ~ r1_xboole_0('#skF_5','#skF_3'('#skF_4','#skF_5','#skF_6'))
    | r2_hidden('#skF_6',k2_pre_topc('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_72407])).

tff(c_72411,plain,(
    ~ r1_xboole_0('#skF_5','#skF_3'('#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_72393,c_72410])).

tff(c_72660,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72405,c_72411])).

tff(c_72662,plain,(
    r2_hidden('#skF_6',k2_pre_topc('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_72392])).

tff(c_72661,plain,(
    r2_hidden('#skF_6',k2_pre_topc('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_72392])).

tff(c_72665,plain,
    ( r2_hidden('#skF_6',k2_tops_1('#skF_4','#skF_5'))
    | ~ r2_hidden('#skF_6',k2_pre_topc('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_72661,c_60091])).

tff(c_72668,plain,(
    r2_hidden('#skF_6',k2_tops_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72662,c_72665])).

tff(c_72670,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_72668])).

tff(c_72671,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_72672,plain,(
    r2_hidden('#skF_6',k2_tops_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_58,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ r2_hidden('#skF_6',k2_tops_1('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_72694,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72672,c_58])).

tff(c_56,plain,
    ( v3_pre_topc('#skF_7','#skF_4')
    | ~ r2_hidden('#skF_6',k2_tops_1('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_72673,plain,(
    ~ r2_hidden('#skF_6',k2_tops_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_72675,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72672,c_72673])).

tff(c_72676,plain,(
    v3_pre_topc('#skF_7','#skF_4') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_78886,plain,(
    ! [A_3754,B_3755] :
      ( m1_subset_1(k2_pre_topc(A_3754,B_3755),k1_zfmisc_1(u1_struct_0(A_3754)))
      | ~ m1_subset_1(B_3755,k1_zfmisc_1(u1_struct_0(A_3754)))
      | ~ l1_pre_topc(A_3754) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_79872,plain,(
    ! [A_3844,B_3845,B_3846] :
      ( k9_subset_1(u1_struct_0(A_3844),B_3845,k2_pre_topc(A_3844,B_3846)) = k3_xboole_0(B_3845,k2_pre_topc(A_3844,B_3846))
      | ~ m1_subset_1(B_3846,k1_zfmisc_1(u1_struct_0(A_3844)))
      | ~ l1_pre_topc(A_3844) ) ),
    inference(resolution,[status(thm)],[c_78886,c_30])).

tff(c_79881,plain,(
    ! [B_3845] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_3845,k2_pre_topc('#skF_4','#skF_5')) = k3_xboole_0(B_3845,k2_pre_topc('#skF_4','#skF_5'))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_79872])).

tff(c_79889,plain,(
    ! [B_3845] : k9_subset_1(u1_struct_0('#skF_4'),B_3845,k2_pre_topc('#skF_4','#skF_5')) = k3_xboole_0(B_3845,k2_pre_topc('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_79881])).

tff(c_80170,plain,(
    ! [A_3860,B_3861,B_3862] :
      ( k9_subset_1(u1_struct_0(A_3860),k2_pre_topc(A_3860,B_3861),B_3862) = k9_subset_1(u1_struct_0(A_3860),B_3862,k2_pre_topc(A_3860,B_3861))
      | ~ m1_subset_1(B_3861,k1_zfmisc_1(u1_struct_0(A_3860)))
      | ~ l1_pre_topc(A_3860) ) ),
    inference(resolution,[status(thm)],[c_78886,c_4])).

tff(c_80179,plain,(
    ! [B_3862] :
      ( k9_subset_1(u1_struct_0('#skF_4'),k2_pre_topc('#skF_4','#skF_5'),B_3862) = k9_subset_1(u1_struct_0('#skF_4'),B_3862,k2_pre_topc('#skF_4','#skF_5'))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_80170])).

tff(c_80188,plain,(
    ! [B_3863] : k9_subset_1(u1_struct_0('#skF_4'),k2_pre_topc('#skF_4','#skF_5'),B_3863) = k3_xboole_0(B_3863,k2_pre_topc('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_79889,c_80179])).

tff(c_80207,plain,
    ( k3_xboole_0(k2_pre_topc('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')),k2_pre_topc('#skF_4','#skF_5')) = k2_tops_1('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_80188,c_6])).

tff(c_80264,plain,(
    k3_xboole_0(k2_pre_topc('#skF_4','#skF_5'),k2_pre_topc('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'))) = k2_tops_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_2,c_80207])).

tff(c_10,plain,(
    ! [D_14,B_10,A_9] :
      ( r2_hidden(D_14,B_10)
      | ~ r2_hidden(D_14,k3_xboole_0(A_9,B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_80472,plain,(
    ! [D_14] :
      ( r2_hidden(D_14,k2_pre_topc('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')))
      | ~ r2_hidden(D_14,k2_tops_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80264,c_10])).

tff(c_72808,plain,(
    ! [A_3478,B_3479] :
      ( m1_subset_1(k2_pre_topc(A_3478,B_3479),k1_zfmisc_1(u1_struct_0(A_3478)))
      | ~ m1_subset_1(B_3479,k1_zfmisc_1(u1_struct_0(A_3478)))
      | ~ l1_pre_topc(A_3478) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_73526,plain,(
    ! [A_3556,B_3557,B_3558] :
      ( k9_subset_1(u1_struct_0(A_3556),B_3557,k2_pre_topc(A_3556,B_3558)) = k3_xboole_0(B_3557,k2_pre_topc(A_3556,B_3558))
      | ~ m1_subset_1(B_3558,k1_zfmisc_1(u1_struct_0(A_3556)))
      | ~ l1_pre_topc(A_3556) ) ),
    inference(resolution,[status(thm)],[c_72808,c_30])).

tff(c_73535,plain,(
    ! [B_3557] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_3557,k2_pre_topc('#skF_4','#skF_5')) = k3_xboole_0(B_3557,k2_pre_topc('#skF_4','#skF_5'))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_73526])).

tff(c_73543,plain,(
    ! [B_3557] : k9_subset_1(u1_struct_0('#skF_4'),B_3557,k2_pre_topc('#skF_4','#skF_5')) = k3_xboole_0(B_3557,k2_pre_topc('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_73535])).

tff(c_73996,plain,(
    ! [A_3574,B_3575,B_3576] :
      ( k9_subset_1(u1_struct_0(A_3574),k2_pre_topc(A_3574,B_3575),B_3576) = k9_subset_1(u1_struct_0(A_3574),B_3576,k2_pre_topc(A_3574,B_3575))
      | ~ m1_subset_1(B_3575,k1_zfmisc_1(u1_struct_0(A_3574)))
      | ~ l1_pre_topc(A_3574) ) ),
    inference(resolution,[status(thm)],[c_72808,c_4])).

tff(c_74005,plain,(
    ! [B_3576] :
      ( k9_subset_1(u1_struct_0('#skF_4'),k2_pre_topc('#skF_4','#skF_5'),B_3576) = k9_subset_1(u1_struct_0('#skF_4'),B_3576,k2_pre_topc('#skF_4','#skF_5'))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_73996])).

tff(c_74155,plain,(
    ! [B_3581] : k9_subset_1(u1_struct_0('#skF_4'),k2_pre_topc('#skF_4','#skF_5'),B_3581) = k3_xboole_0(B_3581,k2_pre_topc('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_73543,c_74005])).

tff(c_74174,plain,
    ( k3_xboole_0(k2_pre_topc('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')),k2_pre_topc('#skF_4','#skF_5')) = k2_tops_1('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_74155,c_6])).

tff(c_74231,plain,(
    k3_xboole_0(k2_pre_topc('#skF_4','#skF_5'),k2_pre_topc('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'))) = k2_tops_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_2,c_74174])).

tff(c_12,plain,(
    ! [D_14,A_9,B_10] :
      ( r2_hidden(D_14,A_9)
      | ~ r2_hidden(D_14,k3_xboole_0(A_9,B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_74644,plain,(
    ! [D_3583] :
      ( r2_hidden(D_3583,k2_pre_topc('#skF_4','#skF_5'))
      | ~ r2_hidden(D_3583,k2_tops_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74231,c_12])).

tff(c_74763,plain,(
    r2_hidden('#skF_6',k2_pre_topc('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_72672,c_74644])).

tff(c_52,plain,
    ( r1_xboole_0(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_7')
    | r1_xboole_0('#skF_5','#skF_7')
    | ~ r2_hidden('#skF_6',k2_tops_1('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_72778,plain,
    ( r1_xboole_0(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_7')
    | r1_xboole_0('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72672,c_52])).

tff(c_72779,plain,(
    r1_xboole_0('#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_72778])).

tff(c_75262,plain,(
    ! [B_3616,D_3617,C_3618,A_3619] :
      ( ~ r1_xboole_0(B_3616,D_3617)
      | ~ r2_hidden(C_3618,D_3617)
      | ~ v3_pre_topc(D_3617,A_3619)
      | ~ m1_subset_1(D_3617,k1_zfmisc_1(u1_struct_0(A_3619)))
      | ~ r2_hidden(C_3618,k2_pre_topc(A_3619,B_3616))
      | ~ m1_subset_1(C_3618,u1_struct_0(A_3619))
      | ~ m1_subset_1(B_3616,k1_zfmisc_1(u1_struct_0(A_3619)))
      | ~ l1_pre_topc(A_3619)
      | ~ v2_pre_topc(A_3619)
      | v2_struct_0(A_3619) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_78447,plain,(
    ! [C_3750,A_3751] :
      ( ~ r2_hidden(C_3750,'#skF_7')
      | ~ v3_pre_topc('#skF_7',A_3751)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(A_3751)))
      | ~ r2_hidden(C_3750,k2_pre_topc(A_3751,'#skF_5'))
      | ~ m1_subset_1(C_3750,u1_struct_0(A_3751))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_3751)))
      | ~ l1_pre_topc(A_3751)
      | ~ v2_pre_topc(A_3751)
      | v2_struct_0(A_3751) ) ),
    inference(resolution,[status(thm)],[c_72779,c_75262])).

tff(c_78449,plain,(
    ! [C_3750] :
      ( ~ r2_hidden(C_3750,'#skF_7')
      | ~ v3_pre_topc('#skF_7','#skF_4')
      | ~ r2_hidden(C_3750,k2_pre_topc('#skF_4','#skF_5'))
      | ~ m1_subset_1(C_3750,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_72694,c_78447])).

tff(c_78452,plain,(
    ! [C_3750] :
      ( ~ r2_hidden(C_3750,'#skF_7')
      | ~ r2_hidden(C_3750,k2_pre_topc('#skF_4','#skF_5'))
      | ~ m1_subset_1(C_3750,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_72676,c_78449])).

tff(c_78454,plain,(
    ! [C_3752] :
      ( ~ r2_hidden(C_3752,'#skF_7')
      | ~ r2_hidden(C_3752,k2_pre_topc('#skF_4','#skF_5'))
      | ~ m1_subset_1(C_3752,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_78452])).

tff(c_78694,plain,
    ( ~ r2_hidden('#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_74763,c_78454])).

tff(c_78854,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_72671,c_78694])).

tff(c_78855,plain,(
    r1_xboole_0(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_72778])).

tff(c_81342,plain,(
    ! [B_3892,D_3893,C_3894,A_3895] :
      ( ~ r1_xboole_0(B_3892,D_3893)
      | ~ r2_hidden(C_3894,D_3893)
      | ~ v3_pre_topc(D_3893,A_3895)
      | ~ m1_subset_1(D_3893,k1_zfmisc_1(u1_struct_0(A_3895)))
      | ~ r2_hidden(C_3894,k2_pre_topc(A_3895,B_3892))
      | ~ m1_subset_1(C_3894,u1_struct_0(A_3895))
      | ~ m1_subset_1(B_3892,k1_zfmisc_1(u1_struct_0(A_3895)))
      | ~ l1_pre_topc(A_3895)
      | ~ v2_pre_topc(A_3895)
      | v2_struct_0(A_3895) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_86974,plain,(
    ! [C_4140,A_4141] :
      ( ~ r2_hidden(C_4140,'#skF_7')
      | ~ v3_pre_topc('#skF_7',A_4141)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(A_4141)))
      | ~ r2_hidden(C_4140,k2_pre_topc(A_4141,k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')))
      | ~ m1_subset_1(C_4140,u1_struct_0(A_4141))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(u1_struct_0(A_4141)))
      | ~ l1_pre_topc(A_4141)
      | ~ v2_pre_topc(A_4141)
      | v2_struct_0(A_4141) ) ),
    inference(resolution,[status(thm)],[c_78855,c_81342])).

tff(c_87240,plain,(
    ! [D_14] :
      ( ~ r2_hidden(D_14,'#skF_7')
      | ~ v3_pre_topc('#skF_7','#skF_4')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(D_14,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r2_hidden(D_14,k2_tops_1('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_80472,c_86974])).

tff(c_87408,plain,(
    ! [D_14] :
      ( ~ r2_hidden(D_14,'#skF_7')
      | ~ m1_subset_1(D_14,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | ~ r2_hidden(D_14,k2_tops_1('#skF_4','#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_72694,c_72676,c_87240])).

tff(c_87409,plain,(
    ! [D_14] :
      ( ~ r2_hidden(D_14,'#skF_7')
      | ~ m1_subset_1(D_14,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r2_hidden(D_14,k2_tops_1('#skF_4','#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_87408])).

tff(c_87434,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_87409])).

tff(c_87437,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_28,c_87434])).

tff(c_87441,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_87437])).

tff(c_87520,plain,(
    ! [D_4143] :
      ( ~ r2_hidden(D_4143,'#skF_7')
      | ~ m1_subset_1(D_4143,u1_struct_0('#skF_4'))
      | ~ r2_hidden(D_4143,k2_tops_1('#skF_4','#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_87409])).

tff(c_87967,plain,
    ( ~ r2_hidden('#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_72672,c_87520])).

tff(c_88084,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_72671,c_87967])).

%------------------------------------------------------------------------------
