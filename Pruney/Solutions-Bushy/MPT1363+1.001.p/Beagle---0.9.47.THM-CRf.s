%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1363+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:51 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 708 expanded)
%              Number of leaves         :   29 ( 275 expanded)
%              Depth                    :   18
%              Number of atoms          :  262 (2726 expanded)
%              Number of equality atoms :   26 ( 129 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_pre_topc > v1_pre_topc > v1_compts_1 > l1_pre_topc > k1_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff(v2_compts_1,type,(
    v2_compts_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_compts_1,type,(
    v1_compts_1: $i > $o )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_138,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v2_compts_1(B,A)
                    & r1_tarski(C,B)
                    & v4_pre_topc(C,A) )
                 => v2_compts_1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_compts_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k1_pre_topc(A,B))
        & m1_pre_topc(k1_pre_topc(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( ( v1_pre_topc(C)
                & m1_pre_topc(C,A) )
             => ( C = k1_pre_topc(A,B)
              <=> k2_struct_0(C) = B ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_pre_topc)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(C,k2_struct_0(B))
               => ( v2_compts_1(C,A)
                <=> ! [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                     => ( D = C
                       => v2_compts_1(D,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_compts_1)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( B = k1_xboole_0
             => ( v2_compts_1(B,A)
              <=> v1_compts_1(k1_pre_topc(A,B)) ) )
            & ( v2_pre_topc(A)
             => ( B = k1_xboole_0
                | ( v2_compts_1(B,A)
                <=> v1_compts_1(k1_pre_topc(A,B)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_compts_1)).

tff(f_102,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v1_compts_1(A)
              & v4_pre_topc(B,A) )
           => v2_compts_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_compts_1)).

tff(f_119,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( v4_pre_topc(B,A)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(C)))
                   => ( D = B
                     => v4_pre_topc(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tops_2)).

tff(c_44,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_42,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_61,plain,(
    ! [A_64,B_65] :
      ( m1_pre_topc(k1_pre_topc(A_64,B_65),A_64)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_65,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_61])).

tff(c_71,plain,(
    m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_65])).

tff(c_34,plain,(
    v4_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_32,plain,(
    ~ v2_compts_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_36,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_48,plain,(
    ! [A_62,B_63] :
      ( v1_pre_topc(k1_pre_topc(A_62,B_63))
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_54,plain,
    ( v1_pre_topc(k1_pre_topc('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_48])).

tff(c_60,plain,(
    v1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_54])).

tff(c_541,plain,(
    ! [A_123,B_124] :
      ( k2_struct_0(k1_pre_topc(A_123,B_124)) = B_124
      | ~ m1_pre_topc(k1_pre_topc(A_123,B_124),A_123)
      | ~ v1_pre_topc(k1_pre_topc(A_123,B_124))
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_pre_topc(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_543,plain,
    ( k2_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_3'
    | ~ v1_pre_topc(k1_pre_topc('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_71,c_541])).

tff(c_548,plain,(
    k2_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_60,c_543])).

tff(c_16,plain,(
    ! [A_13,B_25,C_31] :
      ( '#skF_1'(A_13,B_25,C_31) = C_31
      | v2_compts_1(C_31,A_13)
      | ~ r1_tarski(C_31,k2_struct_0(B_25))
      | ~ m1_subset_1(C_31,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ m1_pre_topc(B_25,A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_648,plain,(
    ! [A_141,C_142] :
      ( '#skF_1'(A_141,k1_pre_topc('#skF_2','#skF_3'),C_142) = C_142
      | v2_compts_1(C_142,A_141)
      | ~ r1_tarski(C_142,'#skF_3')
      | ~ m1_subset_1(C_142,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),A_141)
      | ~ l1_pre_topc(A_141) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_548,c_16])).

tff(c_654,plain,
    ( '#skF_1'('#skF_2',k1_pre_topc('#skF_2','#skF_3'),'#skF_4') = '#skF_4'
    | v2_compts_1('#skF_4','#skF_2')
    | ~ r1_tarski('#skF_4','#skF_3')
    | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_648])).

tff(c_661,plain,
    ( '#skF_1'('#skF_2',k1_pre_topc('#skF_2','#skF_3'),'#skF_4') = '#skF_4'
    | v2_compts_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_71,c_36,c_654])).

tff(c_662,plain,(
    '#skF_1'('#skF_2',k1_pre_topc('#skF_2','#skF_3'),'#skF_4') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_661])).

tff(c_14,plain,(
    ! [A_13,B_25,C_31] :
      ( ~ v2_compts_1('#skF_1'(A_13,B_25,C_31),B_25)
      | v2_compts_1(C_31,A_13)
      | ~ r1_tarski(C_31,k2_struct_0(B_25))
      | ~ m1_subset_1(C_31,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ m1_pre_topc(B_25,A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_671,plain,
    ( ~ v2_compts_1('#skF_4',k1_pre_topc('#skF_2','#skF_3'))
    | v2_compts_1('#skF_4','#skF_2')
    | ~ r1_tarski('#skF_4',k2_struct_0(k1_pre_topc('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_662,c_14])).

tff(c_678,plain,
    ( ~ v2_compts_1('#skF_4',k1_pre_topc('#skF_2','#skF_3'))
    | v2_compts_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_71,c_40,c_36,c_548,c_671])).

tff(c_679,plain,(
    ~ v2_compts_1('#skF_4',k1_pre_topc('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_678])).

tff(c_10,plain,(
    ! [B_12,A_10] :
      ( l1_pre_topc(B_12)
      | ~ m1_pre_topc(B_12,A_10)
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_81,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_71,c_10])).

tff(c_84,plain,(
    l1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_81])).

tff(c_184,plain,(
    ! [A_84,B_85] :
      ( k2_struct_0(k1_pre_topc(A_84,B_85)) = B_85
      | ~ m1_pre_topc(k1_pre_topc(A_84,B_85),A_84)
      | ~ v1_pre_topc(k1_pre_topc(A_84,B_85))
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_pre_topc(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_186,plain,
    ( k2_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_3'
    | ~ v1_pre_topc(k1_pre_topc('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_71,c_184])).

tff(c_191,plain,(
    k2_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_60,c_186])).

tff(c_230,plain,(
    ! [A_88,B_89,C_90] :
      ( '#skF_1'(A_88,B_89,C_90) = C_90
      | v2_compts_1(C_90,A_88)
      | ~ r1_tarski(C_90,k2_struct_0(B_89))
      | ~ m1_subset_1(C_90,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ m1_pre_topc(B_89,A_88)
      | ~ l1_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_292,plain,(
    ! [A_102,C_103] :
      ( '#skF_1'(A_102,k1_pre_topc('#skF_2','#skF_3'),C_103) = C_103
      | v2_compts_1(C_103,A_102)
      | ~ r1_tarski(C_103,'#skF_3')
      | ~ m1_subset_1(C_103,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),A_102)
      | ~ l1_pre_topc(A_102) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_230])).

tff(c_298,plain,
    ( '#skF_1'('#skF_2',k1_pre_topc('#skF_2','#skF_3'),'#skF_4') = '#skF_4'
    | v2_compts_1('#skF_4','#skF_2')
    | ~ r1_tarski('#skF_4','#skF_3')
    | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_292])).

tff(c_305,plain,
    ( '#skF_1'('#skF_2',k1_pre_topc('#skF_2','#skF_3'),'#skF_4') = '#skF_4'
    | v2_compts_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_71,c_36,c_298])).

tff(c_306,plain,(
    '#skF_1'('#skF_2',k1_pre_topc('#skF_2','#skF_3'),'#skF_4') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_305])).

tff(c_315,plain,
    ( ~ v2_compts_1('#skF_4',k1_pre_topc('#skF_2','#skF_3'))
    | v2_compts_1('#skF_4','#skF_2')
    | ~ r1_tarski('#skF_4',k2_struct_0(k1_pre_topc('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_14])).

tff(c_322,plain,
    ( ~ v2_compts_1('#skF_4',k1_pre_topc('#skF_2','#skF_3'))
    | v2_compts_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_71,c_40,c_36,c_191,c_315])).

tff(c_323,plain,(
    ~ v2_compts_1('#skF_4',k1_pre_topc('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_322])).

tff(c_38,plain,(
    v2_compts_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_46,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_100,plain,(
    ! [A_70,B_71] :
      ( v1_compts_1(k1_pre_topc(A_70,B_71))
      | ~ v2_compts_1(B_71,A_70)
      | k1_xboole_0 = B_71
      | ~ v2_pre_topc(A_70)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_106,plain,
    ( v1_compts_1(k1_pre_topc('#skF_2','#skF_3'))
    | ~ v2_compts_1('#skF_3','#skF_2')
    | k1_xboole_0 = '#skF_3'
    | ~ v2_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_100])).

tff(c_112,plain,
    ( v1_compts_1(k1_pre_topc('#skF_2','#skF_3'))
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_38,c_106])).

tff(c_113,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_26,plain,(
    ! [A_35] :
      ( v1_compts_1(k1_pre_topc(A_35,k1_xboole_0))
      | ~ v2_compts_1(k1_xboole_0,A_35)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_129,plain,(
    ! [A_75] :
      ( v1_compts_1(k1_pre_topc(A_75,'#skF_3'))
      | ~ v2_compts_1('#skF_3',A_75)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_113,c_113,c_26])).

tff(c_132,plain,
    ( v1_compts_1(k1_pre_topc('#skF_2','#skF_3'))
    | ~ v2_compts_1('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_129])).

tff(c_135,plain,(
    v1_compts_1(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_38,c_132])).

tff(c_18,plain,(
    ! [A_13,B_25,C_31] :
      ( m1_subset_1('#skF_1'(A_13,B_25,C_31),k1_zfmisc_1(u1_struct_0(B_25)))
      | v2_compts_1(C_31,A_13)
      | ~ r1_tarski(C_31,k2_struct_0(B_25))
      | ~ m1_subset_1(C_31,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ m1_pre_topc(B_25,A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_313,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_2','#skF_3'))))
    | v2_compts_1('#skF_4','#skF_2')
    | ~ r1_tarski('#skF_4',k2_struct_0(k1_pre_topc('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_18])).

tff(c_319,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_2','#skF_3'))))
    | v2_compts_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_71,c_40,c_36,c_191,c_313])).

tff(c_320,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_2','#skF_3')))) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_319])).

tff(c_28,plain,(
    ! [B_40,A_38] :
      ( v2_compts_1(B_40,A_38)
      | ~ v4_pre_topc(B_40,A_38)
      | ~ v1_compts_1(A_38)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_346,plain,
    ( v2_compts_1('#skF_4',k1_pre_topc('#skF_2','#skF_3'))
    | ~ v4_pre_topc('#skF_4',k1_pre_topc('#skF_2','#skF_3'))
    | ~ v1_compts_1(k1_pre_topc('#skF_2','#skF_3'))
    | ~ l1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_320,c_28])).

tff(c_377,plain,
    ( v2_compts_1('#skF_4',k1_pre_topc('#skF_2','#skF_3'))
    | ~ v4_pre_topc('#skF_4',k1_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_135,c_346])).

tff(c_378,plain,(
    ~ v4_pre_topc('#skF_4',k1_pre_topc('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_323,c_377])).

tff(c_30,plain,(
    ! [D_55,C_53,A_41] :
      ( v4_pre_topc(D_55,C_53)
      | ~ m1_subset_1(D_55,k1_zfmisc_1(u1_struct_0(C_53)))
      | ~ v4_pre_topc(D_55,A_41)
      | ~ m1_pre_topc(C_53,A_41)
      | ~ m1_subset_1(D_55,k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ l1_pre_topc(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_367,plain,(
    ! [A_41] :
      ( v4_pre_topc('#skF_4',k1_pre_topc('#skF_2','#skF_3'))
      | ~ v4_pre_topc('#skF_4',A_41)
      | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),A_41)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ l1_pre_topc(A_41) ) ),
    inference(resolution,[status(thm)],[c_320,c_30])).

tff(c_491,plain,(
    ! [A_114] :
      ( ~ v4_pre_topc('#skF_4',A_114)
      | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),A_114)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ l1_pre_topc(A_114) ) ),
    inference(negUnitSimplification,[status(thm)],[c_378,c_367])).

tff(c_497,plain,
    ( ~ v4_pre_topc('#skF_4','#skF_2')
    | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_491])).

tff(c_504,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_71,c_34,c_497])).

tff(c_505,plain,(
    v1_compts_1(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_669,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_2','#skF_3'))))
    | v2_compts_1('#skF_4','#skF_2')
    | ~ r1_tarski('#skF_4',k2_struct_0(k1_pre_topc('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_662,c_18])).

tff(c_675,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_2','#skF_3'))))
    | v2_compts_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_71,c_40,c_36,c_548,c_669])).

tff(c_676,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_2','#skF_3')))) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_675])).

tff(c_702,plain,
    ( v2_compts_1('#skF_4',k1_pre_topc('#skF_2','#skF_3'))
    | ~ v4_pre_topc('#skF_4',k1_pre_topc('#skF_2','#skF_3'))
    | ~ v1_compts_1(k1_pre_topc('#skF_2','#skF_3'))
    | ~ l1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_676,c_28])).

tff(c_733,plain,
    ( v2_compts_1('#skF_4',k1_pre_topc('#skF_2','#skF_3'))
    | ~ v4_pre_topc('#skF_4',k1_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_505,c_702])).

tff(c_734,plain,(
    ~ v4_pre_topc('#skF_4',k1_pre_topc('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_679,c_733])).

tff(c_723,plain,(
    ! [A_41] :
      ( v4_pre_topc('#skF_4',k1_pre_topc('#skF_2','#skF_3'))
      | ~ v4_pre_topc('#skF_4',A_41)
      | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),A_41)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ l1_pre_topc(A_41) ) ),
    inference(resolution,[status(thm)],[c_676,c_30])).

tff(c_847,plain,(
    ! [A_153] :
      ( ~ v4_pre_topc('#skF_4',A_153)
      | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),A_153)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_153)))
      | ~ l1_pre_topc(A_153) ) ),
    inference(negUnitSimplification,[status(thm)],[c_734,c_723])).

tff(c_853,plain,
    ( ~ v4_pre_topc('#skF_4','#skF_2')
    | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_847])).

tff(c_860,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_71,c_34,c_853])).

%------------------------------------------------------------------------------
