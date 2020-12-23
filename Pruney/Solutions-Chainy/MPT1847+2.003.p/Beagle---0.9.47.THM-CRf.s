%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:52 EST 2020

% Result     : Theorem 4.67s
% Output     : CNFRefutation 4.67s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 584 expanded)
%              Number of leaves         :   30 ( 217 expanded)
%              Depth                    :   20
%              Number of atoms          :  191 (1701 expanded)
%              Number of equality atoms :   25 ( 276 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > r1_tarski > m1_subset_1 > m1_pre_topc > l1_pre_topc > k3_xboole_0 > k2_tarski > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(v1_tex_2,type,(
    v1_tex_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_pre_topc(B,A)
           => ! [C] :
                ( m1_pre_topc(C,A)
               => ( ( g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) = g1_pre_topc(u1_struct_0(C),u1_pre_topc(C))
                    & v1_tex_2(B,A) )
                 => v1_tex_2(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_tex_2)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => v1_subset_1(C,u1_struct_0(A)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).

tff(f_40,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => r1_tarski(u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_33,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_28,plain,(
    ~ v1_tex_2('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_38,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_34,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_36,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_30,plain,(
    v1_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_26,plain,(
    ! [A_20,B_26] :
      ( m1_subset_1('#skF_1'(A_20,B_26),k1_zfmisc_1(u1_struct_0(A_20)))
      | v1_tex_2(B_26,A_20)
      | ~ m1_pre_topc(B_26,A_20)
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_93,plain,(
    ! [B_41,A_42] :
      ( l1_pre_topc(B_41)
      | ~ m1_pre_topc(B_41,A_42)
      | ~ l1_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_99,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_93])).

tff(c_106,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_99])).

tff(c_16,plain,(
    ! [A_16] :
      ( m1_pre_topc(A_16,A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_237,plain,(
    ! [B_56,A_57] :
      ( u1_struct_0(B_56) = '#skF_1'(A_57,B_56)
      | v1_tex_2(B_56,A_57)
      | ~ m1_pre_topc(B_56,A_57)
      | ~ l1_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_240,plain,
    ( u1_struct_0('#skF_4') = '#skF_1'('#skF_2','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_237,c_28])).

tff(c_243,plain,(
    u1_struct_0('#skF_4') = '#skF_1'('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_240])).

tff(c_18,plain,(
    ! [B_19,A_17] :
      ( r1_tarski(u1_struct_0(B_19),u1_struct_0(A_17))
      | ~ m1_pre_topc(B_19,A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_267,plain,(
    ! [B_19] :
      ( r1_tarski(u1_struct_0(B_19),'#skF_1'('#skF_2','#skF_4'))
      | ~ m1_pre_topc(B_19,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_18])).

tff(c_281,plain,(
    ! [B_58] :
      ( r1_tarski(u1_struct_0(B_58),'#skF_1'('#skF_2','#skF_4'))
      | ~ m1_pre_topc(B_58,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_267])).

tff(c_287,plain,
    ( r1_tarski('#skF_1'('#skF_2','#skF_4'),'#skF_1'('#skF_2','#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_281])).

tff(c_290,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_287])).

tff(c_302,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_290])).

tff(c_306,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_302])).

tff(c_308,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_287])).

tff(c_377,plain,(
    ! [A_66,B_67] :
      ( m1_pre_topc(A_66,g1_pre_topc(u1_struct_0(B_67),u1_pre_topc(B_67)))
      | ~ m1_pre_topc(A_66,B_67)
      | ~ l1_pre_topc(B_67)
      | ~ l1_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_389,plain,(
    ! [A_66] :
      ( m1_pre_topc(A_66,g1_pre_topc('#skF_1'('#skF_2','#skF_4'),u1_pre_topc('#skF_4')))
      | ~ m1_pre_topc(A_66,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_377])).

tff(c_423,plain,(
    ! [A_70] :
      ( m1_pre_topc(A_70,g1_pre_topc('#skF_1'('#skF_2','#skF_4'),u1_pre_topc('#skF_4')))
      | ~ m1_pre_topc(A_70,'#skF_4')
      | ~ l1_pre_topc(A_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_389])).

tff(c_102,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_93])).

tff(c_109,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_102])).

tff(c_32,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_172,plain,(
    ! [B_49,A_50] :
      ( m1_pre_topc(B_49,A_50)
      | ~ m1_pre_topc(B_49,g1_pre_topc(u1_struct_0(A_50),u1_pre_topc(A_50)))
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_175,plain,(
    ! [B_49] :
      ( m1_pre_topc(B_49,'#skF_3')
      | ~ m1_pre_topc(B_49,g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_172])).

tff(c_181,plain,(
    ! [B_49] :
      ( m1_pre_topc(B_49,'#skF_3')
      | ~ m1_pre_topc(B_49,g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_175])).

tff(c_244,plain,(
    ! [B_49] :
      ( m1_pre_topc(B_49,'#skF_3')
      | ~ m1_pre_topc(B_49,g1_pre_topc('#skF_1'('#skF_2','#skF_4'),u1_pre_topc('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_181])).

tff(c_434,plain,(
    ! [A_70] :
      ( m1_pre_topc(A_70,'#skF_3')
      | ~ m1_pre_topc(A_70,'#skF_4')
      | ~ l1_pre_topc(A_70) ) ),
    inference(resolution,[status(thm)],[c_423,c_244])).

tff(c_245,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = g1_pre_topc('#skF_1'('#skF_2','#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_32])).

tff(c_386,plain,(
    ! [A_66] :
      ( m1_pre_topc(A_66,g1_pre_topc('#skF_1'('#skF_2','#skF_4'),u1_pre_topc('#skF_4')))
      | ~ m1_pre_topc(A_66,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_245,c_377])).

tff(c_396,plain,(
    ! [A_68] :
      ( m1_pre_topc(A_68,g1_pre_topc('#skF_1'('#skF_2','#skF_4'),u1_pre_topc('#skF_4')))
      | ~ m1_pre_topc(A_68,'#skF_3')
      | ~ l1_pre_topc(A_68) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_386])).

tff(c_10,plain,(
    ! [B_12,A_10] :
      ( m1_pre_topc(B_12,A_10)
      | ~ m1_pre_topc(B_12,g1_pre_topc(u1_struct_0(A_10),u1_pre_topc(A_10)))
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_261,plain,(
    ! [B_12] :
      ( m1_pre_topc(B_12,'#skF_4')
      | ~ m1_pre_topc(B_12,g1_pre_topc('#skF_1'('#skF_2','#skF_4'),u1_pre_topc('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_10])).

tff(c_277,plain,(
    ! [B_12] :
      ( m1_pre_topc(B_12,'#skF_4')
      | ~ m1_pre_topc(B_12,g1_pre_topc('#skF_1'('#skF_2','#skF_4'),u1_pre_topc('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_261])).

tff(c_409,plain,(
    ! [A_69] :
      ( m1_pre_topc(A_69,'#skF_4')
      | ~ m1_pre_topc(A_69,'#skF_3')
      | ~ l1_pre_topc(A_69) ) ),
    inference(resolution,[status(thm)],[c_396,c_277])).

tff(c_413,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_409])).

tff(c_416,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_413])).

tff(c_166,plain,(
    ! [B_47,A_48] :
      ( r1_tarski(u1_struct_0(B_47),u1_struct_0(A_48))
      | ~ m1_pre_topc(B_47,A_48)
      | ~ l1_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_170,plain,(
    ! [B_47,A_48] :
      ( k3_xboole_0(u1_struct_0(B_47),u1_struct_0(A_48)) = u1_struct_0(B_47)
      | ~ m1_pre_topc(B_47,A_48)
      | ~ l1_pre_topc(A_48) ) ),
    inference(resolution,[status(thm)],[c_166,c_2])).

tff(c_255,plain,(
    ! [A_48] :
      ( k3_xboole_0('#skF_1'('#skF_2','#skF_4'),u1_struct_0(A_48)) = u1_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_4',A_48)
      | ~ l1_pre_topc(A_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_170])).

tff(c_447,plain,(
    ! [A_72] :
      ( k3_xboole_0('#skF_1'('#skF_2','#skF_4'),u1_struct_0(A_72)) = '#skF_1'('#skF_2','#skF_4')
      | ~ m1_pre_topc('#skF_4',A_72)
      | ~ l1_pre_topc(A_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_255])).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_74,plain,(
    ! [A_39,B_40] : k1_setfam_1(k2_tarski(A_39,B_40)) = k3_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_110,plain,(
    ! [B_43,A_44] : k1_setfam_1(k2_tarski(B_43,A_44)) = k3_xboole_0(A_44,B_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_74])).

tff(c_6,plain,(
    ! [A_5,B_6] : k1_setfam_1(k2_tarski(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_116,plain,(
    ! [B_43,A_44] : k3_xboole_0(B_43,A_44) = k3_xboole_0(A_44,B_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_6])).

tff(c_258,plain,(
    ! [B_47] :
      ( k3_xboole_0(u1_struct_0(B_47),'#skF_1'('#skF_2','#skF_4')) = u1_struct_0(B_47)
      | ~ m1_pre_topc(B_47,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_170])).

tff(c_275,plain,(
    ! [B_47] :
      ( k3_xboole_0('#skF_1'('#skF_2','#skF_4'),u1_struct_0(B_47)) = u1_struct_0(B_47)
      | ~ m1_pre_topc(B_47,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_116,c_258])).

tff(c_467,plain,(
    ! [A_73] :
      ( u1_struct_0(A_73) = '#skF_1'('#skF_2','#skF_4')
      | ~ m1_pre_topc(A_73,'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_73)
      | ~ l1_pre_topc(A_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_447,c_275])).

tff(c_469,plain,
    ( u1_struct_0('#skF_3') = '#skF_1'('#skF_2','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_416,c_467])).

tff(c_477,plain,
    ( u1_struct_0('#skF_3') = '#skF_1'('#skF_2','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_469])).

tff(c_484,plain,(
    ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_477])).

tff(c_487,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_434,c_484])).

tff(c_491,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_308,c_487])).

tff(c_492,plain,(
    u1_struct_0('#skF_3') = '#skF_1'('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_477])).

tff(c_650,plain,(
    ! [B_79,A_80] :
      ( v1_subset_1(u1_struct_0(B_79),u1_struct_0(A_80))
      | ~ m1_subset_1(u1_struct_0(B_79),k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ v1_tex_2(B_79,A_80)
      | ~ m1_pre_topc(B_79,A_80)
      | ~ l1_pre_topc(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_653,plain,(
    ! [A_80] :
      ( v1_subset_1(u1_struct_0('#skF_3'),u1_struct_0(A_80))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ v1_tex_2('#skF_3',A_80)
      | ~ m1_pre_topc('#skF_3',A_80)
      | ~ l1_pre_topc(A_80) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_492,c_650])).

tff(c_1985,plain,(
    ! [A_121] :
      ( v1_subset_1('#skF_1'('#skF_2','#skF_4'),u1_struct_0(A_121))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0(A_121)))
      | ~ v1_tex_2('#skF_3',A_121)
      | ~ m1_pre_topc('#skF_3',A_121)
      | ~ l1_pre_topc(A_121) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_492,c_653])).

tff(c_1992,plain,
    ( v1_subset_1('#skF_1'('#skF_2','#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_tex_2('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | v1_tex_2('#skF_4','#skF_2')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_1985])).

tff(c_2000,plain,
    ( v1_subset_1('#skF_1'('#skF_2','#skF_4'),u1_struct_0('#skF_2'))
    | v1_tex_2('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_36,c_30,c_1992])).

tff(c_2001,plain,(
    v1_subset_1('#skF_1'('#skF_2','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_2000])).

tff(c_22,plain,(
    ! [A_20,B_26] :
      ( ~ v1_subset_1('#skF_1'(A_20,B_26),u1_struct_0(A_20))
      | v1_tex_2(B_26,A_20)
      | ~ m1_pre_topc(B_26,A_20)
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2006,plain,
    ( v1_tex_2('#skF_4','#skF_2')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_2001,c_22])).

tff(c_2009,plain,(
    v1_tex_2('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_2006])).

tff(c_2011,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_2009])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:33:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.67/1.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.67/1.88  
% 4.67/1.88  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.67/1.89  %$ v1_tex_2 > v1_subset_1 > r1_tarski > m1_subset_1 > m1_pre_topc > l1_pre_topc > k3_xboole_0 > k2_tarski > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.67/1.89  
% 4.67/1.89  %Foreground sorts:
% 4.67/1.89  
% 4.67/1.89  
% 4.67/1.89  %Background operators:
% 4.67/1.89  
% 4.67/1.89  
% 4.67/1.89  %Foreground operators:
% 4.67/1.89  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 4.67/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.67/1.89  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 4.67/1.89  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 4.67/1.89  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 4.67/1.89  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.67/1.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.67/1.89  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.67/1.89  tff('#skF_2', type, '#skF_2': $i).
% 4.67/1.89  tff('#skF_3', type, '#skF_3': $i).
% 4.67/1.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.67/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.67/1.89  tff('#skF_4', type, '#skF_4': $i).
% 4.67/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.67/1.89  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.67/1.89  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.67/1.89  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.67/1.89  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.67/1.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.67/1.89  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.67/1.89  
% 4.67/1.90  tff(f_96, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (((g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)) = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C))) & v1_tex_2(B, A)) => v1_tex_2(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_tex_2)).
% 4.67/1.90  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tex_2)).
% 4.67/1.90  tff(f_40, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.67/1.90  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 4.67/1.90  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_borsuk_1)).
% 4.67/1.90  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 4.67/1.90  tff(f_47, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 4.67/1.90  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.67/1.90  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.67/1.90  tff(f_33, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 4.67/1.90  tff(c_28, plain, (~v1_tex_2('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.67/1.90  tff(c_38, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.67/1.90  tff(c_34, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.67/1.90  tff(c_36, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.67/1.90  tff(c_30, plain, (v1_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.67/1.90  tff(c_26, plain, (![A_20, B_26]: (m1_subset_1('#skF_1'(A_20, B_26), k1_zfmisc_1(u1_struct_0(A_20))) | v1_tex_2(B_26, A_20) | ~m1_pre_topc(B_26, A_20) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.67/1.90  tff(c_93, plain, (![B_41, A_42]: (l1_pre_topc(B_41) | ~m1_pre_topc(B_41, A_42) | ~l1_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.67/1.90  tff(c_99, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_34, c_93])).
% 4.67/1.90  tff(c_106, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_99])).
% 4.67/1.90  tff(c_16, plain, (![A_16]: (m1_pre_topc(A_16, A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.67/1.90  tff(c_237, plain, (![B_56, A_57]: (u1_struct_0(B_56)='#skF_1'(A_57, B_56) | v1_tex_2(B_56, A_57) | ~m1_pre_topc(B_56, A_57) | ~l1_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.67/1.90  tff(c_240, plain, (u1_struct_0('#skF_4')='#skF_1'('#skF_2', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_237, c_28])).
% 4.67/1.90  tff(c_243, plain, (u1_struct_0('#skF_4')='#skF_1'('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_240])).
% 4.67/1.90  tff(c_18, plain, (![B_19, A_17]: (r1_tarski(u1_struct_0(B_19), u1_struct_0(A_17)) | ~m1_pre_topc(B_19, A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.67/1.90  tff(c_267, plain, (![B_19]: (r1_tarski(u1_struct_0(B_19), '#skF_1'('#skF_2', '#skF_4')) | ~m1_pre_topc(B_19, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_243, c_18])).
% 4.67/1.90  tff(c_281, plain, (![B_58]: (r1_tarski(u1_struct_0(B_58), '#skF_1'('#skF_2', '#skF_4')) | ~m1_pre_topc(B_58, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_267])).
% 4.67/1.90  tff(c_287, plain, (r1_tarski('#skF_1'('#skF_2', '#skF_4'), '#skF_1'('#skF_2', '#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_243, c_281])).
% 4.67/1.90  tff(c_290, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_287])).
% 4.67/1.90  tff(c_302, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_16, c_290])).
% 4.67/1.90  tff(c_306, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_106, c_302])).
% 4.67/1.90  tff(c_308, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_287])).
% 4.67/1.90  tff(c_377, plain, (![A_66, B_67]: (m1_pre_topc(A_66, g1_pre_topc(u1_struct_0(B_67), u1_pre_topc(B_67))) | ~m1_pre_topc(A_66, B_67) | ~l1_pre_topc(B_67) | ~l1_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.67/1.90  tff(c_389, plain, (![A_66]: (m1_pre_topc(A_66, g1_pre_topc('#skF_1'('#skF_2', '#skF_4'), u1_pre_topc('#skF_4'))) | ~m1_pre_topc(A_66, '#skF_4') | ~l1_pre_topc('#skF_4') | ~l1_pre_topc(A_66))), inference(superposition, [status(thm), theory('equality')], [c_243, c_377])).
% 4.67/1.90  tff(c_423, plain, (![A_70]: (m1_pre_topc(A_70, g1_pre_topc('#skF_1'('#skF_2', '#skF_4'), u1_pre_topc('#skF_4'))) | ~m1_pre_topc(A_70, '#skF_4') | ~l1_pre_topc(A_70))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_389])).
% 4.67/1.90  tff(c_102, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_36, c_93])).
% 4.67/1.90  tff(c_109, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_102])).
% 4.67/1.90  tff(c_32, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.67/1.90  tff(c_172, plain, (![B_49, A_50]: (m1_pre_topc(B_49, A_50) | ~m1_pre_topc(B_49, g1_pre_topc(u1_struct_0(A_50), u1_pre_topc(A_50))) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.67/1.90  tff(c_175, plain, (![B_49]: (m1_pre_topc(B_49, '#skF_3') | ~m1_pre_topc(B_49, g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_32, c_172])).
% 4.67/1.90  tff(c_181, plain, (![B_49]: (m1_pre_topc(B_49, '#skF_3') | ~m1_pre_topc(B_49, g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_175])).
% 4.67/1.90  tff(c_244, plain, (![B_49]: (m1_pre_topc(B_49, '#skF_3') | ~m1_pre_topc(B_49, g1_pre_topc('#skF_1'('#skF_2', '#skF_4'), u1_pre_topc('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_243, c_181])).
% 4.67/1.90  tff(c_434, plain, (![A_70]: (m1_pre_topc(A_70, '#skF_3') | ~m1_pre_topc(A_70, '#skF_4') | ~l1_pre_topc(A_70))), inference(resolution, [status(thm)], [c_423, c_244])).
% 4.67/1.90  tff(c_245, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=g1_pre_topc('#skF_1'('#skF_2', '#skF_4'), u1_pre_topc('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_243, c_32])).
% 4.67/1.90  tff(c_386, plain, (![A_66]: (m1_pre_topc(A_66, g1_pre_topc('#skF_1'('#skF_2', '#skF_4'), u1_pre_topc('#skF_4'))) | ~m1_pre_topc(A_66, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_66))), inference(superposition, [status(thm), theory('equality')], [c_245, c_377])).
% 4.67/1.90  tff(c_396, plain, (![A_68]: (m1_pre_topc(A_68, g1_pre_topc('#skF_1'('#skF_2', '#skF_4'), u1_pre_topc('#skF_4'))) | ~m1_pre_topc(A_68, '#skF_3') | ~l1_pre_topc(A_68))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_386])).
% 4.67/1.90  tff(c_10, plain, (![B_12, A_10]: (m1_pre_topc(B_12, A_10) | ~m1_pre_topc(B_12, g1_pre_topc(u1_struct_0(A_10), u1_pre_topc(A_10))) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.67/1.90  tff(c_261, plain, (![B_12]: (m1_pre_topc(B_12, '#skF_4') | ~m1_pre_topc(B_12, g1_pre_topc('#skF_1'('#skF_2', '#skF_4'), u1_pre_topc('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_243, c_10])).
% 4.67/1.90  tff(c_277, plain, (![B_12]: (m1_pre_topc(B_12, '#skF_4') | ~m1_pre_topc(B_12, g1_pre_topc('#skF_1'('#skF_2', '#skF_4'), u1_pre_topc('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_261])).
% 4.67/1.90  tff(c_409, plain, (![A_69]: (m1_pre_topc(A_69, '#skF_4') | ~m1_pre_topc(A_69, '#skF_3') | ~l1_pre_topc(A_69))), inference(resolution, [status(thm)], [c_396, c_277])).
% 4.67/1.90  tff(c_413, plain, (m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_16, c_409])).
% 4.67/1.90  tff(c_416, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_109, c_413])).
% 4.67/1.90  tff(c_166, plain, (![B_47, A_48]: (r1_tarski(u1_struct_0(B_47), u1_struct_0(A_48)) | ~m1_pre_topc(B_47, A_48) | ~l1_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.67/1.90  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.67/1.90  tff(c_170, plain, (![B_47, A_48]: (k3_xboole_0(u1_struct_0(B_47), u1_struct_0(A_48))=u1_struct_0(B_47) | ~m1_pre_topc(B_47, A_48) | ~l1_pre_topc(A_48))), inference(resolution, [status(thm)], [c_166, c_2])).
% 4.67/1.90  tff(c_255, plain, (![A_48]: (k3_xboole_0('#skF_1'('#skF_2', '#skF_4'), u1_struct_0(A_48))=u1_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', A_48) | ~l1_pre_topc(A_48))), inference(superposition, [status(thm), theory('equality')], [c_243, c_170])).
% 4.67/1.90  tff(c_447, plain, (![A_72]: (k3_xboole_0('#skF_1'('#skF_2', '#skF_4'), u1_struct_0(A_72))='#skF_1'('#skF_2', '#skF_4') | ~m1_pre_topc('#skF_4', A_72) | ~l1_pre_topc(A_72))), inference(demodulation, [status(thm), theory('equality')], [c_243, c_255])).
% 4.67/1.90  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.67/1.90  tff(c_74, plain, (![A_39, B_40]: (k1_setfam_1(k2_tarski(A_39, B_40))=k3_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.67/1.90  tff(c_110, plain, (![B_43, A_44]: (k1_setfam_1(k2_tarski(B_43, A_44))=k3_xboole_0(A_44, B_43))), inference(superposition, [status(thm), theory('equality')], [c_4, c_74])).
% 4.67/1.90  tff(c_6, plain, (![A_5, B_6]: (k1_setfam_1(k2_tarski(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.67/1.90  tff(c_116, plain, (![B_43, A_44]: (k3_xboole_0(B_43, A_44)=k3_xboole_0(A_44, B_43))), inference(superposition, [status(thm), theory('equality')], [c_110, c_6])).
% 4.67/1.90  tff(c_258, plain, (![B_47]: (k3_xboole_0(u1_struct_0(B_47), '#skF_1'('#skF_2', '#skF_4'))=u1_struct_0(B_47) | ~m1_pre_topc(B_47, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_243, c_170])).
% 4.67/1.90  tff(c_275, plain, (![B_47]: (k3_xboole_0('#skF_1'('#skF_2', '#skF_4'), u1_struct_0(B_47))=u1_struct_0(B_47) | ~m1_pre_topc(B_47, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_116, c_258])).
% 4.67/1.90  tff(c_467, plain, (![A_73]: (u1_struct_0(A_73)='#skF_1'('#skF_2', '#skF_4') | ~m1_pre_topc(A_73, '#skF_4') | ~m1_pre_topc('#skF_4', A_73) | ~l1_pre_topc(A_73))), inference(superposition, [status(thm), theory('equality')], [c_447, c_275])).
% 4.67/1.90  tff(c_469, plain, (u1_struct_0('#skF_3')='#skF_1'('#skF_2', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_416, c_467])).
% 4.67/1.90  tff(c_477, plain, (u1_struct_0('#skF_3')='#skF_1'('#skF_2', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_109, c_469])).
% 4.67/1.90  tff(c_484, plain, (~m1_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_477])).
% 4.67/1.90  tff(c_487, plain, (~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_434, c_484])).
% 4.67/1.90  tff(c_491, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_106, c_308, c_487])).
% 4.67/1.90  tff(c_492, plain, (u1_struct_0('#skF_3')='#skF_1'('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_477])).
% 4.67/1.90  tff(c_650, plain, (![B_79, A_80]: (v1_subset_1(u1_struct_0(B_79), u1_struct_0(A_80)) | ~m1_subset_1(u1_struct_0(B_79), k1_zfmisc_1(u1_struct_0(A_80))) | ~v1_tex_2(B_79, A_80) | ~m1_pre_topc(B_79, A_80) | ~l1_pre_topc(A_80))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.67/1.90  tff(c_653, plain, (![A_80]: (v1_subset_1(u1_struct_0('#skF_3'), u1_struct_0(A_80)) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0(A_80))) | ~v1_tex_2('#skF_3', A_80) | ~m1_pre_topc('#skF_3', A_80) | ~l1_pre_topc(A_80))), inference(superposition, [status(thm), theory('equality')], [c_492, c_650])).
% 4.67/1.90  tff(c_1985, plain, (![A_121]: (v1_subset_1('#skF_1'('#skF_2', '#skF_4'), u1_struct_0(A_121)) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0(A_121))) | ~v1_tex_2('#skF_3', A_121) | ~m1_pre_topc('#skF_3', A_121) | ~l1_pre_topc(A_121))), inference(demodulation, [status(thm), theory('equality')], [c_492, c_653])).
% 4.67/1.90  tff(c_1992, plain, (v1_subset_1('#skF_1'('#skF_2', '#skF_4'), u1_struct_0('#skF_2')) | ~v1_tex_2('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | v1_tex_2('#skF_4', '#skF_2') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_26, c_1985])).
% 4.67/1.90  tff(c_2000, plain, (v1_subset_1('#skF_1'('#skF_2', '#skF_4'), u1_struct_0('#skF_2')) | v1_tex_2('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_36, c_30, c_1992])).
% 4.67/1.90  tff(c_2001, plain, (v1_subset_1('#skF_1'('#skF_2', '#skF_4'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_28, c_2000])).
% 4.67/1.90  tff(c_22, plain, (![A_20, B_26]: (~v1_subset_1('#skF_1'(A_20, B_26), u1_struct_0(A_20)) | v1_tex_2(B_26, A_20) | ~m1_pre_topc(B_26, A_20) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.67/1.90  tff(c_2006, plain, (v1_tex_2('#skF_4', '#skF_2') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_2001, c_22])).
% 4.67/1.90  tff(c_2009, plain, (v1_tex_2('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_2006])).
% 4.67/1.90  tff(c_2011, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_2009])).
% 4.67/1.90  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.67/1.90  
% 4.67/1.90  Inference rules
% 4.67/1.90  ----------------------
% 4.67/1.90  #Ref     : 0
% 4.67/1.90  #Sup     : 405
% 4.67/1.90  #Fact    : 0
% 4.67/1.90  #Define  : 0
% 4.67/1.90  #Split   : 9
% 4.67/1.90  #Chain   : 0
% 4.67/1.90  #Close   : 0
% 4.67/1.90  
% 4.67/1.90  Ordering : KBO
% 4.67/1.90  
% 4.67/1.90  Simplification rules
% 4.67/1.90  ----------------------
% 4.67/1.90  #Subsume      : 165
% 4.67/1.90  #Demod        : 1533
% 4.67/1.90  #Tautology    : 163
% 4.67/1.90  #SimpNegUnit  : 24
% 4.67/1.90  #BackRed      : 30
% 4.67/1.90  
% 4.67/1.90  #Partial instantiations: 0
% 4.67/1.90  #Strategies tried      : 1
% 4.67/1.90  
% 4.67/1.90  Timing (in seconds)
% 4.67/1.90  ----------------------
% 4.67/1.91  Preprocessing        : 0.32
% 4.67/1.91  Parsing              : 0.17
% 4.67/1.91  CNF conversion       : 0.02
% 4.67/1.91  Main loop            : 0.81
% 4.67/1.91  Inferencing          : 0.21
% 4.67/1.91  Reduction            : 0.42
% 4.67/1.91  Demodulation         : 0.35
% 4.67/1.91  BG Simplification    : 0.02
% 4.67/1.91  Subsumption          : 0.12
% 4.67/1.91  Abstraction          : 0.03
% 4.67/1.91  MUC search           : 0.00
% 4.67/1.91  Cooper               : 0.00
% 4.67/1.91  Total                : 1.16
% 4.67/1.91  Index Insertion      : 0.00
% 4.67/1.91  Index Deletion       : 0.00
% 4.67/1.91  Index Matching       : 0.00
% 4.67/1.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
