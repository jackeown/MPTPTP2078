%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1221+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:36 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 225 expanded)
%              Number of leaves         :   23 (  86 expanded)
%              Depth                    :   10
%              Number of atoms          :   95 ( 430 expanded)
%              Number of equality atoms :   14 (  76 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > m1_subset_1 > l1_struct_0 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_63,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_28,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(A),k2_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_pre_topc)).

tff(c_18,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_12,plain,(
    ! [A_8] :
      ( l1_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_28,plain,(
    ! [A_14] :
      ( u1_struct_0(A_14) = k2_struct_0(A_14)
      | ~ l1_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_33,plain,(
    ! [A_15] :
      ( u1_struct_0(A_15) = k2_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(resolution,[status(thm)],[c_12,c_28])).

tff(c_37,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_33])).

tff(c_20,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_64,plain,
    ( ~ v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_20])).

tff(c_65,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_16,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_39,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_16])).

tff(c_26,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_66,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_26])).

tff(c_67,plain,(
    v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_66])).

tff(c_68,plain,(
    ! [A_17,B_18] :
      ( k4_xboole_0(A_17,B_18) = k3_subset_1(A_17,B_18)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_79,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2') = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_39,c_68])).

tff(c_10,plain,(
    ! [A_7] :
      ( m1_subset_1(k2_struct_0(A_7),k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ l1_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_43,plain,
    ( m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_10])).

tff(c_47,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_43])).

tff(c_52,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_47])).

tff(c_56,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_52])).

tff(c_57,plain,(
    m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_43])).

tff(c_89,plain,(
    ! [A_19,B_20,C_21] :
      ( k7_subset_1(A_19,B_20,C_21) = k4_xboole_0(B_20,C_21)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_96,plain,(
    ! [C_21] : k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),C_21) = k4_xboole_0(k2_struct_0('#skF_1'),C_21) ),
    inference(resolution,[status(thm)],[c_57,c_89])).

tff(c_145,plain,(
    ! [B_27,A_28] :
      ( v4_pre_topc(B_27,A_28)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(A_28),k2_struct_0(A_28),B_27),A_28)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_151,plain,(
    ! [B_27] :
      ( v4_pre_topc(B_27,'#skF_1')
      | ~ v3_pre_topc(k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),B_27),'#skF_1')
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_145])).

tff(c_167,plain,(
    ! [B_31] :
      ( v4_pre_topc(B_31,'#skF_1')
      | ~ v3_pre_topc(k4_xboole_0(k2_struct_0('#skF_1'),B_31),'#skF_1')
      | ~ m1_subset_1(B_31,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_37,c_96,c_151])).

tff(c_173,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | ~ v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_167])).

tff(c_177,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_67,c_173])).

tff(c_179,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_177])).

tff(c_180,plain,(
    ~ v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_181,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_184,plain,(
    ! [A_32,B_33] :
      ( k4_xboole_0(A_32,B_33) = k3_subset_1(A_32,B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_195,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2') = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_39,c_184])).

tff(c_205,plain,(
    ! [A_34,B_35,C_36] :
      ( k7_subset_1(A_34,B_35,C_36) = k4_xboole_0(B_35,C_36)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_212,plain,(
    ! [C_36] : k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),C_36) = k4_xboole_0(k2_struct_0('#skF_1'),C_36) ),
    inference(resolution,[status(thm)],[c_57,c_205])).

tff(c_224,plain,(
    ! [A_38,B_39] :
      ( v3_pre_topc(k7_subset_1(u1_struct_0(A_38),k2_struct_0(A_38),B_39),A_38)
      | ~ v4_pre_topc(B_39,A_38)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_227,plain,(
    ! [B_39] :
      ( v3_pre_topc(k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),B_39),'#skF_1')
      | ~ v4_pre_topc(B_39,'#skF_1')
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_224])).

tff(c_229,plain,(
    ! [B_39] :
      ( v3_pre_topc(k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),B_39),'#skF_1')
      | ~ v4_pre_topc(B_39,'#skF_1')
      | ~ m1_subset_1(B_39,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_37,c_227])).

tff(c_271,plain,(
    ! [B_44] :
      ( v3_pre_topc(k4_xboole_0(k2_struct_0('#skF_1'),B_44),'#skF_1')
      | ~ v4_pre_topc(B_44,'#skF_1')
      | ~ m1_subset_1(B_44,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_229])).

tff(c_277,plain,
    ( v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_271])).

tff(c_281,plain,(
    v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_181,c_277])).

tff(c_283,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_180,c_281])).

%------------------------------------------------------------------------------
