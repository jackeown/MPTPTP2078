%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:07 EST 2020

% Result     : Theorem 14.47s
% Output     : CNFRefutation 14.47s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 621 expanded)
%              Number of leaves         :   33 ( 222 expanded)
%              Depth                    :   15
%              Number of atoms          :  193 (1642 expanded)
%              Number of equality atoms :   57 ( 443 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_112,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

tff(f_93,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                 => ( ( v3_pre_topc(D,B)
                     => k1_tops_1(B,D) = D )
                    & ( k1_tops_1(A,C) = C
                     => v3_pre_topc(C,A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_100,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_43,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_56,plain,
    ( k7_subset_1(u1_struct_0('#skF_3'),k2_pre_topc('#skF_3','#skF_4'),'#skF_4') != k2_tops_1('#skF_3','#skF_4')
    | ~ v3_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_126,plain,(
    ~ v3_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_54,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_52,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_44,plain,(
    ! [C_41,A_29,D_43,B_37] :
      ( v3_pre_topc(C_41,A_29)
      | k1_tops_1(A_29,C_41) != C_41
      | ~ m1_subset_1(D_43,k1_zfmisc_1(u1_struct_0(B_37)))
      | ~ m1_subset_1(C_41,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ l1_pre_topc(B_37)
      | ~ l1_pre_topc(A_29)
      | ~ v2_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_3449,plain,(
    ! [D_176,B_177] :
      ( ~ m1_subset_1(D_176,k1_zfmisc_1(u1_struct_0(B_177)))
      | ~ l1_pre_topc(B_177) ) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_3452,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_3449])).

tff(c_3456,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_3452])).

tff(c_3465,plain,(
    ! [C_179,A_180] :
      ( v3_pre_topc(C_179,A_180)
      | k1_tops_1(A_180,C_179) != C_179
      | ~ m1_subset_1(C_179,k1_zfmisc_1(u1_struct_0(A_180)))
      | ~ l1_pre_topc(A_180)
      | ~ v2_pre_topc(A_180) ) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_3471,plain,
    ( v3_pre_topc('#skF_4','#skF_3')
    | k1_tops_1('#skF_3','#skF_4') != '#skF_4'
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_3465])).

tff(c_3475,plain,
    ( v3_pre_topc('#skF_4','#skF_3')
    | k1_tops_1('#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_3471])).

tff(c_3476,plain,(
    k1_tops_1('#skF_3','#skF_4') != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_126,c_3475])).

tff(c_1039,plain,(
    ! [A_118,B_119,C_120] :
      ( r2_hidden('#skF_1'(A_118,B_119,C_120),A_118)
      | r2_hidden('#skF_2'(A_118,B_119,C_120),C_120)
      | k4_xboole_0(A_118,B_119) = C_120 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5),C_5)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k4_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1080,plain,(
    ! [A_118,B_119] :
      ( r2_hidden('#skF_2'(A_118,B_119,A_118),A_118)
      | k4_xboole_0(A_118,B_119) = A_118 ) ),
    inference(resolution,[status(thm)],[c_1039,c_16])).

tff(c_321,plain,(
    ! [A_82,B_83,C_84] :
      ( k7_subset_1(A_82,B_83,C_84) = k4_xboole_0(B_83,C_84)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(A_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_324,plain,(
    ! [C_84] : k7_subset_1(u1_struct_0('#skF_3'),'#skF_4',C_84) = k4_xboole_0('#skF_4',C_84) ),
    inference(resolution,[status(thm)],[c_50,c_321])).

tff(c_1304,plain,(
    ! [A_125,B_126] :
      ( k7_subset_1(u1_struct_0(A_125),B_126,k2_tops_1(A_125,B_126)) = k1_tops_1(A_125,B_126)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ l1_pre_topc(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1308,plain,
    ( k7_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_tops_1('#skF_3','#skF_4')) = k1_tops_1('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_1304])).

tff(c_1312,plain,(
    k4_xboole_0('#skF_4',k2_tops_1('#skF_3','#skF_4')) = k1_tops_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_324,c_1308])).

tff(c_533,plain,(
    ! [A_98,B_99] :
      ( m1_subset_1(k2_pre_topc(A_98,B_99),k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ l1_pre_topc(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_36,plain,(
    ! [A_19,B_20,C_21] :
      ( k7_subset_1(A_19,B_20,C_21) = k4_xboole_0(B_20,C_21)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_3959,plain,(
    ! [A_202,B_203,C_204] :
      ( k7_subset_1(u1_struct_0(A_202),k2_pre_topc(A_202,B_203),C_204) = k4_xboole_0(k2_pre_topc(A_202,B_203),C_204)
      | ~ m1_subset_1(B_203,k1_zfmisc_1(u1_struct_0(A_202)))
      | ~ l1_pre_topc(A_202) ) ),
    inference(resolution,[status(thm)],[c_533,c_36])).

tff(c_3963,plain,(
    ! [C_204] :
      ( k7_subset_1(u1_struct_0('#skF_3'),k2_pre_topc('#skF_3','#skF_4'),C_204) = k4_xboole_0(k2_pre_topc('#skF_3','#skF_4'),C_204)
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_3959])).

tff(c_3968,plain,(
    ! [C_205] : k7_subset_1(u1_struct_0('#skF_3'),k2_pre_topc('#skF_3','#skF_4'),C_205) = k4_xboole_0(k2_pre_topc('#skF_3','#skF_4'),C_205) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_3963])).

tff(c_62,plain,
    ( v3_pre_topc('#skF_4','#skF_3')
    | k7_subset_1(u1_struct_0('#skF_3'),k2_pre_topc('#skF_3','#skF_4'),'#skF_4') = k2_tops_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_213,plain,(
    k7_subset_1(u1_struct_0('#skF_3'),k2_pre_topc('#skF_3','#skF_4'),'#skF_4') = k2_tops_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_126,c_62])).

tff(c_3978,plain,(
    k4_xboole_0(k2_pre_topc('#skF_3','#skF_4'),'#skF_4') = k2_tops_1('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3968,c_213])).

tff(c_1998,plain,(
    ! [A_142,B_143,C_144] :
      ( r2_hidden('#skF_1'(A_142,B_143,C_144),A_142)
      | r2_hidden('#skF_2'(A_142,B_143,C_144),B_143)
      | ~ r2_hidden('#skF_2'(A_142,B_143,C_144),A_142)
      | k4_xboole_0(A_142,B_143) = C_144 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( ~ r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_9451,plain,(
    ! [A_279,A_280,B_281,C_282] :
      ( ~ r2_hidden('#skF_2'(A_279,k4_xboole_0(A_280,B_281),C_282),B_281)
      | r2_hidden('#skF_1'(A_279,k4_xboole_0(A_280,B_281),C_282),A_279)
      | ~ r2_hidden('#skF_2'(A_279,k4_xboole_0(A_280,B_281),C_282),A_279)
      | k4_xboole_0(A_279,k4_xboole_0(A_280,B_281)) = C_282 ) ),
    inference(resolution,[status(thm)],[c_1998,c_6])).

tff(c_30009,plain,(
    ! [A_468,A_469] :
      ( r2_hidden('#skF_1'(A_468,k4_xboole_0(A_469,A_468),A_468),A_468)
      | ~ r2_hidden('#skF_2'(A_468,k4_xboole_0(A_469,A_468),A_468),A_468)
      | k4_xboole_0(A_468,k4_xboole_0(A_469,A_468)) = A_468 ) ),
    inference(resolution,[status(thm)],[c_1080,c_9451])).

tff(c_30220,plain,
    ( r2_hidden('#skF_1'('#skF_4',k2_tops_1('#skF_3','#skF_4'),'#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_2'('#skF_4',k4_xboole_0(k2_pre_topc('#skF_3','#skF_4'),'#skF_4'),'#skF_4'),'#skF_4')
    | k4_xboole_0('#skF_4',k4_xboole_0(k2_pre_topc('#skF_3','#skF_4'),'#skF_4')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_3978,c_30009])).

tff(c_30299,plain,
    ( r2_hidden('#skF_1'('#skF_4',k2_tops_1('#skF_3','#skF_4'),'#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_2'('#skF_4',k2_tops_1('#skF_3','#skF_4'),'#skF_4'),'#skF_4')
    | k1_tops_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1312,c_3978,c_3978,c_30220])).

tff(c_30300,plain,
    ( r2_hidden('#skF_1'('#skF_4',k2_tops_1('#skF_3','#skF_4'),'#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_2'('#skF_4',k2_tops_1('#skF_3','#skF_4'),'#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_3476,c_30299])).

tff(c_30307,plain,(
    ~ r2_hidden('#skF_2'('#skF_4',k2_tops_1('#skF_3','#skF_4'),'#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_30300])).

tff(c_30312,plain,(
    k4_xboole_0('#skF_4',k2_tops_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1080,c_30307])).

tff(c_30313,plain,(
    k1_tops_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30312,c_1312])).

tff(c_30315,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3476,c_30313])).

tff(c_30317,plain,(
    r2_hidden('#skF_2'('#skF_4',k2_tops_1('#skF_3','#skF_4'),'#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_30300])).

tff(c_30316,plain,(
    r2_hidden('#skF_1'('#skF_4',k2_tops_1('#skF_3','#skF_4'),'#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_30300])).

tff(c_10,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5),C_5)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),B_4)
      | ~ r2_hidden('#skF_2'(A_3,B_4,C_5),A_3)
      | k4_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_30319,plain,
    ( r2_hidden('#skF_2'('#skF_4',k2_tops_1('#skF_3','#skF_4'),'#skF_4'),k2_tops_1('#skF_3','#skF_4'))
    | ~ r2_hidden('#skF_2'('#skF_4',k2_tops_1('#skF_3','#skF_4'),'#skF_4'),'#skF_4')
    | k4_xboole_0('#skF_4',k2_tops_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_30316,c_10])).

tff(c_30324,plain,
    ( r2_hidden('#skF_2'('#skF_4',k2_tops_1('#skF_3','#skF_4'),'#skF_4'),k2_tops_1('#skF_3','#skF_4'))
    | ~ r2_hidden('#skF_2'('#skF_4',k2_tops_1('#skF_3','#skF_4'),'#skF_4'),'#skF_4')
    | k1_tops_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1312,c_30319])).

tff(c_30325,plain,
    ( r2_hidden('#skF_2'('#skF_4',k2_tops_1('#skF_3','#skF_4'),'#skF_4'),k2_tops_1('#skF_3','#skF_4'))
    | ~ r2_hidden('#skF_2'('#skF_4',k2_tops_1('#skF_3','#skF_4'),'#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_3476,c_30324])).

tff(c_31592,plain,(
    r2_hidden('#skF_2'('#skF_4',k2_tops_1('#skF_3','#skF_4'),'#skF_4'),k2_tops_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30317,c_30325])).

tff(c_4034,plain,(
    ! [D_8] :
      ( ~ r2_hidden(D_8,'#skF_4')
      | ~ r2_hidden(D_8,k2_tops_1('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3978,c_6])).

tff(c_31598,plain,(
    ~ r2_hidden('#skF_2'('#skF_4',k2_tops_1('#skF_3','#skF_4'),'#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_31592,c_4034])).

tff(c_31606,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30317,c_31598])).

tff(c_31607,plain,(
    k7_subset_1(u1_struct_0('#skF_3'),k2_pre_topc('#skF_3','#skF_4'),'#skF_4') != k2_tops_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_26,plain,(
    ! [B_10] : r1_tarski(B_10,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_31608,plain,(
    v3_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_46,plain,(
    ! [B_37,D_43,C_41,A_29] :
      ( k1_tops_1(B_37,D_43) = D_43
      | ~ v3_pre_topc(D_43,B_37)
      | ~ m1_subset_1(D_43,k1_zfmisc_1(u1_struct_0(B_37)))
      | ~ m1_subset_1(C_41,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ l1_pre_topc(B_37)
      | ~ l1_pre_topc(A_29)
      | ~ v2_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_33594,plain,(
    ! [C_571,A_572] :
      ( ~ m1_subset_1(C_571,k1_zfmisc_1(u1_struct_0(A_572)))
      | ~ l1_pre_topc(A_572)
      | ~ v2_pre_topc(A_572) ) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_33600,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_33594])).

tff(c_33605,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_33600])).

tff(c_33805,plain,(
    ! [B_579,D_580] :
      ( k1_tops_1(B_579,D_580) = D_580
      | ~ v3_pre_topc(D_580,B_579)
      | ~ m1_subset_1(D_580,k1_zfmisc_1(u1_struct_0(B_579)))
      | ~ l1_pre_topc(B_579) ) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_33811,plain,
    ( k1_tops_1('#skF_3','#skF_4') = '#skF_4'
    | ~ v3_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_33805])).

tff(c_33815,plain,(
    k1_tops_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_31608,c_33811])).

tff(c_31995,plain,(
    ! [A_516,B_517,C_518] :
      ( k7_subset_1(A_516,B_517,C_518) = k4_xboole_0(B_517,C_518)
      | ~ m1_subset_1(B_517,k1_zfmisc_1(A_516)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_31998,plain,(
    ! [C_518] : k7_subset_1(u1_struct_0('#skF_3'),'#skF_4',C_518) = k4_xboole_0('#skF_4',C_518) ),
    inference(resolution,[status(thm)],[c_50,c_31995])).

tff(c_32565,plain,(
    ! [A_543,B_544] :
      ( k7_subset_1(u1_struct_0(A_543),B_544,k2_tops_1(A_543,B_544)) = k1_tops_1(A_543,B_544)
      | ~ m1_subset_1(B_544,k1_zfmisc_1(u1_struct_0(A_543)))
      | ~ l1_pre_topc(A_543) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_32569,plain,
    ( k7_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_tops_1('#skF_3','#skF_4')) = k1_tops_1('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_32565])).

tff(c_32573,plain,(
    k4_xboole_0('#skF_4',k2_tops_1('#skF_3','#skF_4')) = k1_tops_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_31998,c_32569])).

tff(c_32,plain,(
    ! [A_15,B_16] : r1_tarski(k4_xboole_0(A_15,B_16),A_15) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_31696,plain,(
    ! [B_495,A_496] :
      ( B_495 = A_496
      | ~ r1_tarski(B_495,A_496)
      | ~ r1_tarski(A_496,B_495) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_33505,plain,(
    ! [A_567,B_568] :
      ( k4_xboole_0(A_567,B_568) = A_567
      | ~ r1_tarski(A_567,k4_xboole_0(A_567,B_568)) ) ),
    inference(resolution,[status(thm)],[c_32,c_31696])).

tff(c_33514,plain,
    ( k4_xboole_0('#skF_4',k2_tops_1('#skF_3','#skF_4')) = '#skF_4'
    | ~ r1_tarski('#skF_4',k1_tops_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_32573,c_33505])).

tff(c_33523,plain,
    ( k1_tops_1('#skF_3','#skF_4') = '#skF_4'
    | ~ r1_tarski('#skF_4',k1_tops_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32573,c_33514])).

tff(c_33592,plain,(
    ~ r1_tarski('#skF_4',k1_tops_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_33523])).

tff(c_33816,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33815,c_33592])).

tff(c_33828,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_33816])).

tff(c_33829,plain,(
    k1_tops_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_33523])).

tff(c_42,plain,(
    ! [A_26,B_28] :
      ( k7_subset_1(u1_struct_0(A_26),k2_pre_topc(A_26,B_28),k1_tops_1(A_26,B_28)) = k2_tops_1(A_26,B_28)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_33847,plain,
    ( k7_subset_1(u1_struct_0('#skF_3'),k2_pre_topc('#skF_3','#skF_4'),'#skF_4') = k2_tops_1('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_33829,c_42])).

tff(c_33851,plain,(
    k7_subset_1(u1_struct_0('#skF_3'),k2_pre_topc('#skF_3','#skF_4'),'#skF_4') = k2_tops_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_33847])).

tff(c_33853,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_31607,c_33851])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:03:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.47/7.00  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.47/7.01  
% 14.47/7.01  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.47/7.01  %$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 14.47/7.01  
% 14.47/7.01  %Foreground sorts:
% 14.47/7.01  
% 14.47/7.01  
% 14.47/7.01  %Background operators:
% 14.47/7.01  
% 14.47/7.01  
% 14.47/7.01  %Foreground operators:
% 14.47/7.01  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 14.47/7.01  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 14.47/7.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.47/7.01  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.47/7.01  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 14.47/7.01  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 14.47/7.01  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 14.47/7.01  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 14.47/7.01  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.47/7.01  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 14.47/7.01  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 14.47/7.01  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 14.47/7.01  tff('#skF_3', type, '#skF_3': $i).
% 14.47/7.01  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 14.47/7.01  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.47/7.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.47/7.01  tff('#skF_4', type, '#skF_4': $i).
% 14.47/7.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.47/7.01  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 14.47/7.01  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.47/7.01  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 14.47/7.01  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 14.47/7.01  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.47/7.01  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 14.47/7.01  
% 14.47/7.03  tff(f_112, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tops_1)).
% 14.47/7.03  tff(f_93, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tops_1)).
% 14.47/7.03  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 14.47/7.03  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 14.47/7.03  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 14.47/7.03  tff(f_65, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 14.47/7.03  tff(f_43, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 14.47/7.03  tff(f_51, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 14.47/7.03  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 14.47/7.03  tff(c_56, plain, (k7_subset_1(u1_struct_0('#skF_3'), k2_pre_topc('#skF_3', '#skF_4'), '#skF_4')!=k2_tops_1('#skF_3', '#skF_4') | ~v3_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 14.47/7.03  tff(c_126, plain, (~v3_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_56])).
% 14.47/7.03  tff(c_54, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 14.47/7.03  tff(c_52, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 14.47/7.03  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 14.47/7.03  tff(c_44, plain, (![C_41, A_29, D_43, B_37]: (v3_pre_topc(C_41, A_29) | k1_tops_1(A_29, C_41)!=C_41 | ~m1_subset_1(D_43, k1_zfmisc_1(u1_struct_0(B_37))) | ~m1_subset_1(C_41, k1_zfmisc_1(u1_struct_0(A_29))) | ~l1_pre_topc(B_37) | ~l1_pre_topc(A_29) | ~v2_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_93])).
% 14.47/7.03  tff(c_3449, plain, (![D_176, B_177]: (~m1_subset_1(D_176, k1_zfmisc_1(u1_struct_0(B_177))) | ~l1_pre_topc(B_177))), inference(splitLeft, [status(thm)], [c_44])).
% 14.47/7.03  tff(c_3452, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_50, c_3449])).
% 14.47/7.03  tff(c_3456, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_3452])).
% 14.47/7.03  tff(c_3465, plain, (![C_179, A_180]: (v3_pre_topc(C_179, A_180) | k1_tops_1(A_180, C_179)!=C_179 | ~m1_subset_1(C_179, k1_zfmisc_1(u1_struct_0(A_180))) | ~l1_pre_topc(A_180) | ~v2_pre_topc(A_180))), inference(splitRight, [status(thm)], [c_44])).
% 14.47/7.03  tff(c_3471, plain, (v3_pre_topc('#skF_4', '#skF_3') | k1_tops_1('#skF_3', '#skF_4')!='#skF_4' | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_50, c_3465])).
% 14.47/7.03  tff(c_3475, plain, (v3_pre_topc('#skF_4', '#skF_3') | k1_tops_1('#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_3471])).
% 14.47/7.03  tff(c_3476, plain, (k1_tops_1('#skF_3', '#skF_4')!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_126, c_3475])).
% 14.47/7.03  tff(c_1039, plain, (![A_118, B_119, C_120]: (r2_hidden('#skF_1'(A_118, B_119, C_120), A_118) | r2_hidden('#skF_2'(A_118, B_119, C_120), C_120) | k4_xboole_0(A_118, B_119)=C_120)), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.47/7.03  tff(c_16, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_1'(A_3, B_4, C_5), C_5) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k4_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.47/7.03  tff(c_1080, plain, (![A_118, B_119]: (r2_hidden('#skF_2'(A_118, B_119, A_118), A_118) | k4_xboole_0(A_118, B_119)=A_118)), inference(resolution, [status(thm)], [c_1039, c_16])).
% 14.47/7.03  tff(c_321, plain, (![A_82, B_83, C_84]: (k7_subset_1(A_82, B_83, C_84)=k4_xboole_0(B_83, C_84) | ~m1_subset_1(B_83, k1_zfmisc_1(A_82)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 14.47/7.03  tff(c_324, plain, (![C_84]: (k7_subset_1(u1_struct_0('#skF_3'), '#skF_4', C_84)=k4_xboole_0('#skF_4', C_84))), inference(resolution, [status(thm)], [c_50, c_321])).
% 14.47/7.03  tff(c_1304, plain, (![A_125, B_126]: (k7_subset_1(u1_struct_0(A_125), B_126, k2_tops_1(A_125, B_126))=k1_tops_1(A_125, B_126) | ~m1_subset_1(B_126, k1_zfmisc_1(u1_struct_0(A_125))) | ~l1_pre_topc(A_125))), inference(cnfTransformation, [status(thm)], [f_100])).
% 14.47/7.03  tff(c_1308, plain, (k7_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_tops_1('#skF_3', '#skF_4'))=k1_tops_1('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_50, c_1304])).
% 14.47/7.03  tff(c_1312, plain, (k4_xboole_0('#skF_4', k2_tops_1('#skF_3', '#skF_4'))=k1_tops_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_324, c_1308])).
% 14.47/7.03  tff(c_533, plain, (![A_98, B_99]: (m1_subset_1(k2_pre_topc(A_98, B_99), k1_zfmisc_1(u1_struct_0(A_98))) | ~m1_subset_1(B_99, k1_zfmisc_1(u1_struct_0(A_98))) | ~l1_pre_topc(A_98))), inference(cnfTransformation, [status(thm)], [f_65])).
% 14.47/7.03  tff(c_36, plain, (![A_19, B_20, C_21]: (k7_subset_1(A_19, B_20, C_21)=k4_xboole_0(B_20, C_21) | ~m1_subset_1(B_20, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 14.47/7.03  tff(c_3959, plain, (![A_202, B_203, C_204]: (k7_subset_1(u1_struct_0(A_202), k2_pre_topc(A_202, B_203), C_204)=k4_xboole_0(k2_pre_topc(A_202, B_203), C_204) | ~m1_subset_1(B_203, k1_zfmisc_1(u1_struct_0(A_202))) | ~l1_pre_topc(A_202))), inference(resolution, [status(thm)], [c_533, c_36])).
% 14.47/7.03  tff(c_3963, plain, (![C_204]: (k7_subset_1(u1_struct_0('#skF_3'), k2_pre_topc('#skF_3', '#skF_4'), C_204)=k4_xboole_0(k2_pre_topc('#skF_3', '#skF_4'), C_204) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_3959])).
% 14.47/7.03  tff(c_3968, plain, (![C_205]: (k7_subset_1(u1_struct_0('#skF_3'), k2_pre_topc('#skF_3', '#skF_4'), C_205)=k4_xboole_0(k2_pre_topc('#skF_3', '#skF_4'), C_205))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_3963])).
% 14.47/7.03  tff(c_62, plain, (v3_pre_topc('#skF_4', '#skF_3') | k7_subset_1(u1_struct_0('#skF_3'), k2_pre_topc('#skF_3', '#skF_4'), '#skF_4')=k2_tops_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_112])).
% 14.47/7.03  tff(c_213, plain, (k7_subset_1(u1_struct_0('#skF_3'), k2_pre_topc('#skF_3', '#skF_4'), '#skF_4')=k2_tops_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_126, c_62])).
% 14.47/7.03  tff(c_3978, plain, (k4_xboole_0(k2_pre_topc('#skF_3', '#skF_4'), '#skF_4')=k2_tops_1('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3968, c_213])).
% 14.47/7.03  tff(c_1998, plain, (![A_142, B_143, C_144]: (r2_hidden('#skF_1'(A_142, B_143, C_144), A_142) | r2_hidden('#skF_2'(A_142, B_143, C_144), B_143) | ~r2_hidden('#skF_2'(A_142, B_143, C_144), A_142) | k4_xboole_0(A_142, B_143)=C_144)), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.47/7.03  tff(c_6, plain, (![D_8, B_4, A_3]: (~r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.47/7.03  tff(c_9451, plain, (![A_279, A_280, B_281, C_282]: (~r2_hidden('#skF_2'(A_279, k4_xboole_0(A_280, B_281), C_282), B_281) | r2_hidden('#skF_1'(A_279, k4_xboole_0(A_280, B_281), C_282), A_279) | ~r2_hidden('#skF_2'(A_279, k4_xboole_0(A_280, B_281), C_282), A_279) | k4_xboole_0(A_279, k4_xboole_0(A_280, B_281))=C_282)), inference(resolution, [status(thm)], [c_1998, c_6])).
% 14.47/7.03  tff(c_30009, plain, (![A_468, A_469]: (r2_hidden('#skF_1'(A_468, k4_xboole_0(A_469, A_468), A_468), A_468) | ~r2_hidden('#skF_2'(A_468, k4_xboole_0(A_469, A_468), A_468), A_468) | k4_xboole_0(A_468, k4_xboole_0(A_469, A_468))=A_468)), inference(resolution, [status(thm)], [c_1080, c_9451])).
% 14.47/7.03  tff(c_30220, plain, (r2_hidden('#skF_1'('#skF_4', k2_tops_1('#skF_3', '#skF_4'), '#skF_4'), '#skF_4') | ~r2_hidden('#skF_2'('#skF_4', k4_xboole_0(k2_pre_topc('#skF_3', '#skF_4'), '#skF_4'), '#skF_4'), '#skF_4') | k4_xboole_0('#skF_4', k4_xboole_0(k2_pre_topc('#skF_3', '#skF_4'), '#skF_4'))='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_3978, c_30009])).
% 14.47/7.03  tff(c_30299, plain, (r2_hidden('#skF_1'('#skF_4', k2_tops_1('#skF_3', '#skF_4'), '#skF_4'), '#skF_4') | ~r2_hidden('#skF_2'('#skF_4', k2_tops_1('#skF_3', '#skF_4'), '#skF_4'), '#skF_4') | k1_tops_1('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1312, c_3978, c_3978, c_30220])).
% 14.47/7.03  tff(c_30300, plain, (r2_hidden('#skF_1'('#skF_4', k2_tops_1('#skF_3', '#skF_4'), '#skF_4'), '#skF_4') | ~r2_hidden('#skF_2'('#skF_4', k2_tops_1('#skF_3', '#skF_4'), '#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_3476, c_30299])).
% 14.47/7.03  tff(c_30307, plain, (~r2_hidden('#skF_2'('#skF_4', k2_tops_1('#skF_3', '#skF_4'), '#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_30300])).
% 14.47/7.03  tff(c_30312, plain, (k4_xboole_0('#skF_4', k2_tops_1('#skF_3', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_1080, c_30307])).
% 14.47/7.03  tff(c_30313, plain, (k1_tops_1('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_30312, c_1312])).
% 14.47/7.03  tff(c_30315, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3476, c_30313])).
% 14.47/7.03  tff(c_30317, plain, (r2_hidden('#skF_2'('#skF_4', k2_tops_1('#skF_3', '#skF_4'), '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_30300])).
% 14.47/7.03  tff(c_30316, plain, (r2_hidden('#skF_1'('#skF_4', k2_tops_1('#skF_3', '#skF_4'), '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_30300])).
% 14.47/7.03  tff(c_10, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_1'(A_3, B_4, C_5), C_5) | r2_hidden('#skF_2'(A_3, B_4, C_5), B_4) | ~r2_hidden('#skF_2'(A_3, B_4, C_5), A_3) | k4_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.47/7.03  tff(c_30319, plain, (r2_hidden('#skF_2'('#skF_4', k2_tops_1('#skF_3', '#skF_4'), '#skF_4'), k2_tops_1('#skF_3', '#skF_4')) | ~r2_hidden('#skF_2'('#skF_4', k2_tops_1('#skF_3', '#skF_4'), '#skF_4'), '#skF_4') | k4_xboole_0('#skF_4', k2_tops_1('#skF_3', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_30316, c_10])).
% 14.47/7.03  tff(c_30324, plain, (r2_hidden('#skF_2'('#skF_4', k2_tops_1('#skF_3', '#skF_4'), '#skF_4'), k2_tops_1('#skF_3', '#skF_4')) | ~r2_hidden('#skF_2'('#skF_4', k2_tops_1('#skF_3', '#skF_4'), '#skF_4'), '#skF_4') | k1_tops_1('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1312, c_30319])).
% 14.47/7.03  tff(c_30325, plain, (r2_hidden('#skF_2'('#skF_4', k2_tops_1('#skF_3', '#skF_4'), '#skF_4'), k2_tops_1('#skF_3', '#skF_4')) | ~r2_hidden('#skF_2'('#skF_4', k2_tops_1('#skF_3', '#skF_4'), '#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_3476, c_30324])).
% 14.47/7.03  tff(c_31592, plain, (r2_hidden('#skF_2'('#skF_4', k2_tops_1('#skF_3', '#skF_4'), '#skF_4'), k2_tops_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_30317, c_30325])).
% 14.47/7.03  tff(c_4034, plain, (![D_8]: (~r2_hidden(D_8, '#skF_4') | ~r2_hidden(D_8, k2_tops_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_3978, c_6])).
% 14.47/7.03  tff(c_31598, plain, (~r2_hidden('#skF_2'('#skF_4', k2_tops_1('#skF_3', '#skF_4'), '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_31592, c_4034])).
% 14.47/7.03  tff(c_31606, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30317, c_31598])).
% 14.47/7.03  tff(c_31607, plain, (k7_subset_1(u1_struct_0('#skF_3'), k2_pre_topc('#skF_3', '#skF_4'), '#skF_4')!=k2_tops_1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_56])).
% 14.47/7.03  tff(c_26, plain, (![B_10]: (r1_tarski(B_10, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 14.47/7.03  tff(c_31608, plain, (v3_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_56])).
% 14.47/7.03  tff(c_46, plain, (![B_37, D_43, C_41, A_29]: (k1_tops_1(B_37, D_43)=D_43 | ~v3_pre_topc(D_43, B_37) | ~m1_subset_1(D_43, k1_zfmisc_1(u1_struct_0(B_37))) | ~m1_subset_1(C_41, k1_zfmisc_1(u1_struct_0(A_29))) | ~l1_pre_topc(B_37) | ~l1_pre_topc(A_29) | ~v2_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_93])).
% 14.47/7.03  tff(c_33594, plain, (![C_571, A_572]: (~m1_subset_1(C_571, k1_zfmisc_1(u1_struct_0(A_572))) | ~l1_pre_topc(A_572) | ~v2_pre_topc(A_572))), inference(splitLeft, [status(thm)], [c_46])).
% 14.47/7.03  tff(c_33600, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_50, c_33594])).
% 14.47/7.03  tff(c_33605, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_33600])).
% 14.47/7.03  tff(c_33805, plain, (![B_579, D_580]: (k1_tops_1(B_579, D_580)=D_580 | ~v3_pre_topc(D_580, B_579) | ~m1_subset_1(D_580, k1_zfmisc_1(u1_struct_0(B_579))) | ~l1_pre_topc(B_579))), inference(splitRight, [status(thm)], [c_46])).
% 14.47/7.03  tff(c_33811, plain, (k1_tops_1('#skF_3', '#skF_4')='#skF_4' | ~v3_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_50, c_33805])).
% 14.47/7.03  tff(c_33815, plain, (k1_tops_1('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_31608, c_33811])).
% 14.47/7.03  tff(c_31995, plain, (![A_516, B_517, C_518]: (k7_subset_1(A_516, B_517, C_518)=k4_xboole_0(B_517, C_518) | ~m1_subset_1(B_517, k1_zfmisc_1(A_516)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 14.47/7.03  tff(c_31998, plain, (![C_518]: (k7_subset_1(u1_struct_0('#skF_3'), '#skF_4', C_518)=k4_xboole_0('#skF_4', C_518))), inference(resolution, [status(thm)], [c_50, c_31995])).
% 14.47/7.03  tff(c_32565, plain, (![A_543, B_544]: (k7_subset_1(u1_struct_0(A_543), B_544, k2_tops_1(A_543, B_544))=k1_tops_1(A_543, B_544) | ~m1_subset_1(B_544, k1_zfmisc_1(u1_struct_0(A_543))) | ~l1_pre_topc(A_543))), inference(cnfTransformation, [status(thm)], [f_100])).
% 14.47/7.03  tff(c_32569, plain, (k7_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_tops_1('#skF_3', '#skF_4'))=k1_tops_1('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_50, c_32565])).
% 14.47/7.03  tff(c_32573, plain, (k4_xboole_0('#skF_4', k2_tops_1('#skF_3', '#skF_4'))=k1_tops_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_31998, c_32569])).
% 14.47/7.03  tff(c_32, plain, (![A_15, B_16]: (r1_tarski(k4_xboole_0(A_15, B_16), A_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 14.47/7.03  tff(c_31696, plain, (![B_495, A_496]: (B_495=A_496 | ~r1_tarski(B_495, A_496) | ~r1_tarski(A_496, B_495))), inference(cnfTransformation, [status(thm)], [f_43])).
% 14.47/7.03  tff(c_33505, plain, (![A_567, B_568]: (k4_xboole_0(A_567, B_568)=A_567 | ~r1_tarski(A_567, k4_xboole_0(A_567, B_568)))), inference(resolution, [status(thm)], [c_32, c_31696])).
% 14.47/7.03  tff(c_33514, plain, (k4_xboole_0('#skF_4', k2_tops_1('#skF_3', '#skF_4'))='#skF_4' | ~r1_tarski('#skF_4', k1_tops_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_32573, c_33505])).
% 14.47/7.03  tff(c_33523, plain, (k1_tops_1('#skF_3', '#skF_4')='#skF_4' | ~r1_tarski('#skF_4', k1_tops_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_32573, c_33514])).
% 14.47/7.03  tff(c_33592, plain, (~r1_tarski('#skF_4', k1_tops_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_33523])).
% 14.47/7.03  tff(c_33816, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_33815, c_33592])).
% 14.47/7.03  tff(c_33828, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_33816])).
% 14.47/7.03  tff(c_33829, plain, (k1_tops_1('#skF_3', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_33523])).
% 14.47/7.03  tff(c_42, plain, (![A_26, B_28]: (k7_subset_1(u1_struct_0(A_26), k2_pre_topc(A_26, B_28), k1_tops_1(A_26, B_28))=k2_tops_1(A_26, B_28) | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_72])).
% 14.47/7.03  tff(c_33847, plain, (k7_subset_1(u1_struct_0('#skF_3'), k2_pre_topc('#skF_3', '#skF_4'), '#skF_4')=k2_tops_1('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_33829, c_42])).
% 14.47/7.03  tff(c_33851, plain, (k7_subset_1(u1_struct_0('#skF_3'), k2_pre_topc('#skF_3', '#skF_4'), '#skF_4')=k2_tops_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_33847])).
% 14.47/7.03  tff(c_33853, plain, $false, inference(negUnitSimplification, [status(thm)], [c_31607, c_33851])).
% 14.47/7.03  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.47/7.03  
% 14.47/7.03  Inference rules
% 14.47/7.03  ----------------------
% 14.47/7.03  #Ref     : 0
% 14.47/7.03  #Sup     : 8823
% 14.47/7.03  #Fact    : 0
% 14.47/7.03  #Define  : 0
% 14.47/7.03  #Split   : 9
% 14.47/7.03  #Chain   : 0
% 14.47/7.03  #Close   : 0
% 14.47/7.03  
% 14.47/7.03  Ordering : KBO
% 14.47/7.03  
% 14.47/7.03  Simplification rules
% 14.47/7.03  ----------------------
% 14.47/7.03  #Subsume      : 1993
% 14.47/7.03  #Demod        : 9683
% 14.47/7.03  #Tautology    : 2635
% 14.47/7.03  #SimpNegUnit  : 10
% 14.47/7.03  #BackRed      : 26
% 14.47/7.03  
% 14.47/7.03  #Partial instantiations: 0
% 14.47/7.03  #Strategies tried      : 1
% 14.47/7.03  
% 14.47/7.03  Timing (in seconds)
% 14.47/7.03  ----------------------
% 14.47/7.04  Preprocessing        : 0.34
% 14.47/7.04  Parsing              : 0.17
% 14.47/7.04  CNF conversion       : 0.03
% 14.47/7.04  Main loop            : 5.92
% 14.47/7.04  Inferencing          : 0.96
% 14.47/7.04  Reduction            : 3.31
% 14.47/7.04  Demodulation         : 2.97
% 14.47/7.04  BG Simplification    : 0.14
% 14.47/7.04  Subsumption          : 1.27
% 14.47/7.04  Abstraction          : 0.23
% 14.47/7.04  MUC search           : 0.00
% 14.47/7.04  Cooper               : 0.00
% 14.47/7.04  Total                : 6.30
% 14.47/7.04  Index Insertion      : 0.00
% 14.47/7.04  Index Deletion       : 0.00
% 14.47/7.04  Index Matching       : 0.00
% 14.47/7.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
