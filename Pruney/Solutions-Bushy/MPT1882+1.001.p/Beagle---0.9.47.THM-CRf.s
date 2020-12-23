%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1882+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:37 EST 2020

% Result     : Theorem 2.72s
% Output     : CNFRefutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 257 expanded)
%              Number of leaves         :   24 (  99 expanded)
%              Depth                    :   11
%              Number of atoms          :  195 ( 985 expanded)
%              Number of equality atoms :    9 (  45 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_105,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v2_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ( v3_tex_2(B,A)
            <=> v1_zfmisc_1(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tex_2)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tex_2(B,A)
          <=> ( v2_tex_2(B,A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( v2_tex_2(C,A)
                      & r1_tarski(B,C) )
                   => B = C ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

tff(f_85,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v2_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ( v2_tex_2(B,A)
          <=> v1_zfmisc_1(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_62,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_28,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_38,plain,
    ( ~ v1_zfmisc_1('#skF_3')
    | ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_45,plain,(
    ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_30,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_94,plain,(
    ! [A_35,B_36] :
      ( '#skF_1'(A_35,B_36) != B_36
      | v3_tex_2(B_36,A_35)
      | ~ v2_tex_2(B_36,A_35)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_101,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_94])).

tff(c_105,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_101])).

tff(c_106,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_105])).

tff(c_107,plain,(
    ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_34,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_32,plain,(
    v2_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_44,plain,
    ( v3_tex_2('#skF_3','#skF_2')
    | v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_46,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_44])).

tff(c_226,plain,(
    ! [B_57,A_58] :
      ( v2_tex_2(B_57,A_58)
      | ~ v1_zfmisc_1(B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_58)))
      | v1_xboole_0(B_57)
      | ~ l1_pre_topc(A_58)
      | ~ v2_tdlat_3(A_58)
      | ~ v2_pre_topc(A_58)
      | v2_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_236,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_226])).

tff(c_241,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_46,c_236])).

tff(c_243,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_28,c_107,c_241])).

tff(c_245,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_272,plain,(
    ! [B_65,A_66] :
      ( r1_tarski(B_65,'#skF_1'(A_66,B_65))
      | v3_tex_2(B_65,A_66)
      | ~ v2_tex_2(B_65,A_66)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_277,plain,
    ( r1_tarski('#skF_3','#skF_1'('#skF_2','#skF_3'))
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_272])).

tff(c_281,plain,
    ( r1_tarski('#skF_3','#skF_1'('#skF_2','#skF_3'))
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_245,c_277])).

tff(c_282,plain,(
    r1_tarski('#skF_3','#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_281])).

tff(c_20,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(A_17,k1_zfmisc_1(B_18))
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_57,plain,(
    ! [B_27,A_28] :
      ( v1_xboole_0(B_27)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(A_28))
      | ~ v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_64,plain,(
    ! [A_17,B_18] :
      ( v1_xboole_0(A_17)
      | ~ v1_xboole_0(B_18)
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(resolution,[status(thm)],[c_20,c_57])).

tff(c_288,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_282,c_64])).

tff(c_294,plain,(
    ~ v1_xboole_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_288])).

tff(c_244,plain,(
    '#skF_1'('#skF_2','#skF_3') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_16,plain,(
    ! [B_16,A_14] :
      ( B_16 = A_14
      | ~ r1_tarski(A_14,B_16)
      | ~ v1_zfmisc_1(B_16)
      | v1_xboole_0(B_16)
      | v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_285,plain,
    ( '#skF_1'('#skF_2','#skF_3') = '#skF_3'
    | ~ v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_282,c_16])).

tff(c_291,plain,
    ( ~ v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_244,c_285])).

tff(c_295,plain,(
    ~ v1_zfmisc_1('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_294,c_291])).

tff(c_246,plain,(
    ! [A_59,B_60] :
      ( v2_tex_2('#skF_1'(A_59,B_60),A_59)
      | v3_tex_2(B_60,A_59)
      | ~ v2_tex_2(B_60,A_59)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_251,plain,
    ( v2_tex_2('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_246])).

tff(c_255,plain,
    ( v2_tex_2('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_245,c_251])).

tff(c_256,plain,(
    v2_tex_2('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_255])).

tff(c_325,plain,(
    ! [A_75,B_76] :
      ( m1_subset_1('#skF_1'(A_75,B_76),k1_zfmisc_1(u1_struct_0(A_75)))
      | v3_tex_2(B_76,A_75)
      | ~ v2_tex_2(B_76,A_75)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_24,plain,(
    ! [B_21,A_19] :
      ( v1_zfmisc_1(B_21)
      | ~ v2_tex_2(B_21,A_19)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_19)))
      | v1_xboole_0(B_21)
      | ~ l1_pre_topc(A_19)
      | ~ v2_tdlat_3(A_19)
      | ~ v2_pre_topc(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_520,plain,(
    ! [A_102,B_103] :
      ( v1_zfmisc_1('#skF_1'(A_102,B_103))
      | ~ v2_tex_2('#skF_1'(A_102,B_103),A_102)
      | v1_xboole_0('#skF_1'(A_102,B_103))
      | ~ v2_tdlat_3(A_102)
      | ~ v2_pre_topc(A_102)
      | v2_struct_0(A_102)
      | v3_tex_2(B_103,A_102)
      | ~ v2_tex_2(B_103,A_102)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102) ) ),
    inference(resolution,[status(thm)],[c_325,c_24])).

tff(c_526,plain,
    ( v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3'))
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_256,c_520])).

tff(c_531,plain,
    ( v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2')
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_245,c_34,c_32,c_526])).

tff(c_533,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_36,c_294,c_295,c_531])).

tff(c_534,plain,(
    ~ v1_zfmisc_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_535,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_573,plain,(
    ! [B_114,A_115] :
      ( v2_tex_2(B_114,A_115)
      | ~ v3_tex_2(B_114,A_115)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_pre_topc(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_580,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | ~ v3_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_573])).

tff(c_584,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_535,c_580])).

tff(c_638,plain,(
    ! [B_130,A_131] :
      ( v1_zfmisc_1(B_130)
      | ~ v2_tex_2(B_130,A_131)
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0(A_131)))
      | v1_xboole_0(B_130)
      | ~ l1_pre_topc(A_131)
      | ~ v2_tdlat_3(A_131)
      | ~ v2_pre_topc(A_131)
      | v2_struct_0(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_645,plain,
    ( v1_zfmisc_1('#skF_3')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_638])).

tff(c_649,plain,
    ( v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_584,c_645])).

tff(c_651,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_28,c_534,c_649])).

%------------------------------------------------------------------------------
