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
% DateTime   : Thu Dec  3 10:30:16 EST 2020

% Result     : Theorem 8.81s
% Output     : CNFRefutation 8.81s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 346 expanded)
%              Number of leaves         :   32 ( 128 expanded)
%              Depth                    :   13
%              Number of atoms          :  224 (1290 expanded)
%              Number of equality atoms :   21 (  89 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > k2_xboole_0 > #nlpp > u1_struct_0 > o_1_1_filter_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(o_1_1_filter_1,type,(
    o_1_1_filter_1: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

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

tff(f_148,negated_conjecture,(
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

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_zfmisc_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_zfmisc_1)).

tff(f_82,axiom,(
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

tff(f_128,axiom,(
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

tff(f_95,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_38,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_14,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_60,plain,
    ( ~ v1_zfmisc_1('#skF_3')
    | ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_71,plain,(
    ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_18,plain,(
    ! [A_10] :
      ( v1_zfmisc_1(A_10)
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_52,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_48,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_353,plain,(
    ! [A_71,B_72] :
      ( '#skF_1'(A_71,B_72) != B_72
      | v3_tex_2(B_72,A_71)
      | ~ v2_tex_2(B_72,A_71)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_364,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_353])).

tff(c_371,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_364])).

tff(c_372,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_371])).

tff(c_373,plain,(
    ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_372])).

tff(c_56,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_54,plain,(
    v2_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_66,plain,
    ( v3_tex_2('#skF_3','#skF_2')
    | v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_82,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_66])).

tff(c_859,plain,(
    ! [B_97,A_98] :
      ( v2_tex_2(B_97,A_98)
      | ~ v1_zfmisc_1(B_97)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0(A_98)))
      | v1_xboole_0(B_97)
      | ~ l1_pre_topc(A_98)
      | ~ v2_tdlat_3(A_98)
      | ~ v2_pre_topc(A_98)
      | v2_struct_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_893,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_859])).

tff(c_908,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_82,c_893])).

tff(c_910,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_50,c_373,c_908])).

tff(c_911,plain,(
    '#skF_1'('#skF_2','#skF_3') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_372])).

tff(c_912,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_372])).

tff(c_934,plain,(
    ! [B_100,A_101] :
      ( r1_tarski(B_100,'#skF_1'(A_101,B_100))
      | v3_tex_2(B_100,A_101)
      | ~ v2_tex_2(B_100,A_101)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_pre_topc(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_945,plain,
    ( r1_tarski('#skF_3','#skF_1'('#skF_2','#skF_3'))
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_934])).

tff(c_953,plain,
    ( r1_tarski('#skF_3','#skF_1'('#skF_2','#skF_3'))
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_912,c_945])).

tff(c_954,plain,(
    r1_tarski('#skF_3','#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_953])).

tff(c_40,plain,(
    ! [B_27,A_25] :
      ( B_27 = A_25
      | ~ r1_tarski(A_25,B_27)
      | ~ v1_zfmisc_1(B_27)
      | v1_xboole_0(B_27)
      | v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_959,plain,
    ( '#skF_1'('#skF_2','#skF_3') = '#skF_3'
    | ~ v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_954,c_40])).

tff(c_967,plain,
    ( ~ v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_911,c_959])).

tff(c_971,plain,(
    ~ v1_zfmisc_1('#skF_1'('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_967])).

tff(c_975,plain,(
    ~ v1_xboole_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_18,c_971])).

tff(c_976,plain,(
    ! [A_102,B_103] :
      ( v2_tex_2('#skF_1'(A_102,B_103),A_102)
      | v3_tex_2(B_103,A_102)
      | ~ v2_tex_2(B_103,A_102)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_987,plain,
    ( v2_tex_2('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_976])).

tff(c_995,plain,
    ( v2_tex_2('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_912,c_987])).

tff(c_996,plain,(
    v2_tex_2('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_995])).

tff(c_34,plain,(
    ! [A_15,B_21] :
      ( m1_subset_1('#skF_1'(A_15,B_21),k1_zfmisc_1(u1_struct_0(A_15)))
      | v3_tex_2(B_21,A_15)
      | ~ v2_tex_2(B_21,A_15)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1323,plain,(
    ! [B_121,A_122] :
      ( v1_zfmisc_1(B_121)
      | ~ v2_tex_2(B_121,A_122)
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0(A_122)))
      | v1_xboole_0(B_121)
      | ~ l1_pre_topc(A_122)
      | ~ v2_tdlat_3(A_122)
      | ~ v2_pre_topc(A_122)
      | v2_struct_0(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_6513,plain,(
    ! [A_278,B_279] :
      ( v1_zfmisc_1('#skF_1'(A_278,B_279))
      | ~ v2_tex_2('#skF_1'(A_278,B_279),A_278)
      | v1_xboole_0('#skF_1'(A_278,B_279))
      | ~ v2_tdlat_3(A_278)
      | ~ v2_pre_topc(A_278)
      | v2_struct_0(A_278)
      | v3_tex_2(B_279,A_278)
      | ~ v2_tex_2(B_279,A_278)
      | ~ m1_subset_1(B_279,k1_zfmisc_1(u1_struct_0(A_278)))
      | ~ l1_pre_topc(A_278) ) ),
    inference(resolution,[status(thm)],[c_34,c_1323])).

tff(c_6527,plain,
    ( v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3'))
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_996,c_6513])).

tff(c_6539,plain,
    ( v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2')
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_912,c_56,c_54,c_6527])).

tff(c_6541,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_58,c_975,c_971,c_6539])).

tff(c_6542,plain,(
    v1_xboole_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_967])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_84,plain,(
    ! [B_41,A_42] :
      ( ~ v1_xboole_0(B_41)
      | B_41 = A_42
      | ~ v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_87,plain,(
    ! [A_42] :
      ( k1_xboole_0 = A_42
      | ~ v1_xboole_0(A_42) ) ),
    inference(resolution,[status(thm)],[c_2,c_84])).

tff(c_6549,plain,(
    '#skF_1'('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6542,c_87])).

tff(c_12,plain,(
    ! [A_6] : k2_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_10,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,k2_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_137,plain,(
    ! [B_55,A_56] :
      ( B_55 = A_56
      | ~ r1_tarski(B_55,A_56)
      | ~ r1_tarski(A_56,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_285,plain,(
    ! [C_65,B_66,A_67] :
      ( k2_xboole_0(C_65,B_66) = A_67
      | ~ r1_tarski(k2_xboole_0(C_65,B_66),A_67)
      | ~ r1_tarski(A_67,B_66) ) ),
    inference(resolution,[status(thm)],[c_10,c_137])).

tff(c_292,plain,(
    ! [A_6,A_67] :
      ( k2_xboole_0(A_6,k1_xboole_0) = A_67
      | ~ r1_tarski(A_6,A_67)
      | ~ r1_tarski(A_67,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_285])).

tff(c_298,plain,(
    ! [A_67,A_6] :
      ( A_67 = A_6
      | ~ r1_tarski(A_6,A_67)
      | ~ r1_tarski(A_67,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_292])).

tff(c_956,plain,
    ( '#skF_1'('#skF_2','#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_1'('#skF_2','#skF_3'),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_954,c_298])).

tff(c_964,plain,(
    ~ r1_tarski('#skF_1'('#skF_2','#skF_3'),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_911,c_956])).

tff(c_6553,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6549,c_964])).

tff(c_6560,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_6553])).

tff(c_6561,plain,(
    ~ v1_zfmisc_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_6562,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_6725,plain,(
    ! [B_302,A_303] :
      ( v2_tex_2(B_302,A_303)
      | ~ v3_tex_2(B_302,A_303)
      | ~ m1_subset_1(B_302,k1_zfmisc_1(u1_struct_0(A_303)))
      | ~ l1_pre_topc(A_303) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_6736,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | ~ v3_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_6725])).

tff(c_6743,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_6562,c_6736])).

tff(c_7356,plain,(
    ! [B_341,A_342] :
      ( v1_zfmisc_1(B_341)
      | ~ v2_tex_2(B_341,A_342)
      | ~ m1_subset_1(B_341,k1_zfmisc_1(u1_struct_0(A_342)))
      | v1_xboole_0(B_341)
      | ~ l1_pre_topc(A_342)
      | ~ v2_tdlat_3(A_342)
      | ~ v2_pre_topc(A_342)
      | v2_struct_0(A_342) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_7387,plain,
    ( v1_zfmisc_1('#skF_3')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_7356])).

tff(c_7401,plain,
    ( v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_6743,c_7387])).

tff(c_7403,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_50,c_6561,c_7401])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:29:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.81/3.04  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.81/3.04  
% 8.81/3.04  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.81/3.05  %$ v3_tex_2 > v2_tex_2 > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > k2_xboole_0 > #nlpp > u1_struct_0 > o_1_1_filter_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 8.81/3.05  
% 8.81/3.05  %Foreground sorts:
% 8.81/3.05  
% 8.81/3.05  
% 8.81/3.05  %Background operators:
% 8.81/3.05  
% 8.81/3.05  
% 8.81/3.05  %Foreground operators:
% 8.81/3.05  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.81/3.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.81/3.05  tff(o_1_1_filter_1, type, o_1_1_filter_1: $i > $i).
% 8.81/3.05  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.81/3.05  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.81/3.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.81/3.05  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 8.81/3.05  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 8.81/3.05  tff('#skF_2', type, '#skF_2': $i).
% 8.81/3.05  tff('#skF_3', type, '#skF_3': $i).
% 8.81/3.05  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.81/3.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.81/3.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.81/3.05  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 8.81/3.05  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.81/3.05  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.81/3.05  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.81/3.05  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.81/3.05  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.81/3.05  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 8.81/3.05  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.81/3.05  
% 8.81/3.06  tff(f_148, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v3_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_tex_2)).
% 8.81/3.06  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.81/3.06  tff(f_52, axiom, (![A]: (v1_xboole_0(A) => v1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_zfmisc_1)).
% 8.81/3.06  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 8.81/3.06  tff(f_128, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tex_2)).
% 8.81/3.06  tff(f_95, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 8.81/3.06  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 8.81/3.06  tff(f_48, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 8.81/3.06  tff(f_38, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 8.81/3.06  tff(f_36, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 8.81/3.06  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.81/3.06  tff(c_58, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_148])).
% 8.81/3.06  tff(c_50, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_148])).
% 8.81/3.06  tff(c_14, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 8.81/3.06  tff(c_60, plain, (~v1_zfmisc_1('#skF_3') | ~v3_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_148])).
% 8.81/3.06  tff(c_71, plain, (~v3_tex_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_60])).
% 8.81/3.06  tff(c_18, plain, (![A_10]: (v1_zfmisc_1(A_10) | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.81/3.06  tff(c_52, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_148])).
% 8.81/3.06  tff(c_48, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_148])).
% 8.81/3.06  tff(c_353, plain, (![A_71, B_72]: ('#skF_1'(A_71, B_72)!=B_72 | v3_tex_2(B_72, A_71) | ~v2_tex_2(B_72, A_71) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.81/3.06  tff(c_364, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3' | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_48, c_353])).
% 8.81/3.06  tff(c_371, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3' | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_364])).
% 8.81/3.06  tff(c_372, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3' | ~v2_tex_2('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_71, c_371])).
% 8.81/3.06  tff(c_373, plain, (~v2_tex_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_372])).
% 8.81/3.06  tff(c_56, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_148])).
% 8.81/3.06  tff(c_54, plain, (v2_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_148])).
% 8.81/3.06  tff(c_66, plain, (v3_tex_2('#skF_3', '#skF_2') | v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_148])).
% 8.81/3.06  tff(c_82, plain, (v1_zfmisc_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_71, c_66])).
% 8.81/3.06  tff(c_859, plain, (![B_97, A_98]: (v2_tex_2(B_97, A_98) | ~v1_zfmisc_1(B_97) | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0(A_98))) | v1_xboole_0(B_97) | ~l1_pre_topc(A_98) | ~v2_tdlat_3(A_98) | ~v2_pre_topc(A_98) | v2_struct_0(A_98))), inference(cnfTransformation, [status(thm)], [f_128])).
% 8.81/3.06  tff(c_893, plain, (v2_tex_2('#skF_3', '#skF_2') | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_859])).
% 8.81/3.06  tff(c_908, plain, (v2_tex_2('#skF_3', '#skF_2') | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_82, c_893])).
% 8.81/3.06  tff(c_910, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_50, c_373, c_908])).
% 8.81/3.06  tff(c_911, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3'), inference(splitRight, [status(thm)], [c_372])).
% 8.81/3.06  tff(c_912, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_372])).
% 8.81/3.06  tff(c_934, plain, (![B_100, A_101]: (r1_tarski(B_100, '#skF_1'(A_101, B_100)) | v3_tex_2(B_100, A_101) | ~v2_tex_2(B_100, A_101) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(A_101))) | ~l1_pre_topc(A_101))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.81/3.06  tff(c_945, plain, (r1_tarski('#skF_3', '#skF_1'('#skF_2', '#skF_3')) | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_48, c_934])).
% 8.81/3.06  tff(c_953, plain, (r1_tarski('#skF_3', '#skF_1'('#skF_2', '#skF_3')) | v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_912, c_945])).
% 8.81/3.06  tff(c_954, plain, (r1_tarski('#skF_3', '#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_71, c_953])).
% 8.81/3.06  tff(c_40, plain, (![B_27, A_25]: (B_27=A_25 | ~r1_tarski(A_25, B_27) | ~v1_zfmisc_1(B_27) | v1_xboole_0(B_27) | v1_xboole_0(A_25))), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.81/3.06  tff(c_959, plain, ('#skF_1'('#skF_2', '#skF_3')='#skF_3' | ~v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_954, c_40])).
% 8.81/3.06  tff(c_967, plain, (~v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_50, c_911, c_959])).
% 8.81/3.06  tff(c_971, plain, (~v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_967])).
% 8.81/3.06  tff(c_975, plain, (~v1_xboole_0('#skF_1'('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_18, c_971])).
% 8.81/3.06  tff(c_976, plain, (![A_102, B_103]: (v2_tex_2('#skF_1'(A_102, B_103), A_102) | v3_tex_2(B_103, A_102) | ~v2_tex_2(B_103, A_102) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.81/3.06  tff(c_987, plain, (v2_tex_2('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_48, c_976])).
% 8.81/3.06  tff(c_995, plain, (v2_tex_2('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_912, c_987])).
% 8.81/3.06  tff(c_996, plain, (v2_tex_2('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_71, c_995])).
% 8.81/3.06  tff(c_34, plain, (![A_15, B_21]: (m1_subset_1('#skF_1'(A_15, B_21), k1_zfmisc_1(u1_struct_0(A_15))) | v3_tex_2(B_21, A_15) | ~v2_tex_2(B_21, A_15) | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.81/3.06  tff(c_1323, plain, (![B_121, A_122]: (v1_zfmisc_1(B_121) | ~v2_tex_2(B_121, A_122) | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0(A_122))) | v1_xboole_0(B_121) | ~l1_pre_topc(A_122) | ~v2_tdlat_3(A_122) | ~v2_pre_topc(A_122) | v2_struct_0(A_122))), inference(cnfTransformation, [status(thm)], [f_128])).
% 8.81/3.06  tff(c_6513, plain, (![A_278, B_279]: (v1_zfmisc_1('#skF_1'(A_278, B_279)) | ~v2_tex_2('#skF_1'(A_278, B_279), A_278) | v1_xboole_0('#skF_1'(A_278, B_279)) | ~v2_tdlat_3(A_278) | ~v2_pre_topc(A_278) | v2_struct_0(A_278) | v3_tex_2(B_279, A_278) | ~v2_tex_2(B_279, A_278) | ~m1_subset_1(B_279, k1_zfmisc_1(u1_struct_0(A_278))) | ~l1_pre_topc(A_278))), inference(resolution, [status(thm)], [c_34, c_1323])).
% 8.81/3.06  tff(c_6527, plain, (v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_1'('#skF_2', '#skF_3')) | ~v2_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_996, c_6513])).
% 8.81/3.06  tff(c_6539, plain, (v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_2') | v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_912, c_56, c_54, c_6527])).
% 8.81/3.06  tff(c_6541, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_58, c_975, c_971, c_6539])).
% 8.81/3.06  tff(c_6542, plain, (v1_xboole_0('#skF_1'('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_967])).
% 8.81/3.06  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 8.81/3.06  tff(c_84, plain, (![B_41, A_42]: (~v1_xboole_0(B_41) | B_41=A_42 | ~v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_48])).
% 8.81/3.06  tff(c_87, plain, (![A_42]: (k1_xboole_0=A_42 | ~v1_xboole_0(A_42))), inference(resolution, [status(thm)], [c_2, c_84])).
% 8.81/3.06  tff(c_6549, plain, ('#skF_1'('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_6542, c_87])).
% 8.81/3.06  tff(c_12, plain, (![A_6]: (k2_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.81/3.06  tff(c_10, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, k2_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.81/3.06  tff(c_137, plain, (![B_55, A_56]: (B_55=A_56 | ~r1_tarski(B_55, A_56) | ~r1_tarski(A_56, B_55))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.81/3.06  tff(c_285, plain, (![C_65, B_66, A_67]: (k2_xboole_0(C_65, B_66)=A_67 | ~r1_tarski(k2_xboole_0(C_65, B_66), A_67) | ~r1_tarski(A_67, B_66))), inference(resolution, [status(thm)], [c_10, c_137])).
% 8.81/3.06  tff(c_292, plain, (![A_6, A_67]: (k2_xboole_0(A_6, k1_xboole_0)=A_67 | ~r1_tarski(A_6, A_67) | ~r1_tarski(A_67, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_285])).
% 8.81/3.06  tff(c_298, plain, (![A_67, A_6]: (A_67=A_6 | ~r1_tarski(A_6, A_67) | ~r1_tarski(A_67, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_292])).
% 8.81/3.06  tff(c_956, plain, ('#skF_1'('#skF_2', '#skF_3')='#skF_3' | ~r1_tarski('#skF_1'('#skF_2', '#skF_3'), k1_xboole_0)), inference(resolution, [status(thm)], [c_954, c_298])).
% 8.81/3.06  tff(c_964, plain, (~r1_tarski('#skF_1'('#skF_2', '#skF_3'), k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_911, c_956])).
% 8.81/3.06  tff(c_6553, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6549, c_964])).
% 8.81/3.06  tff(c_6560, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_6553])).
% 8.81/3.06  tff(c_6561, plain, (~v1_zfmisc_1('#skF_3')), inference(splitRight, [status(thm)], [c_60])).
% 8.81/3.06  tff(c_6562, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_60])).
% 8.81/3.06  tff(c_6725, plain, (![B_302, A_303]: (v2_tex_2(B_302, A_303) | ~v3_tex_2(B_302, A_303) | ~m1_subset_1(B_302, k1_zfmisc_1(u1_struct_0(A_303))) | ~l1_pre_topc(A_303))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.81/3.06  tff(c_6736, plain, (v2_tex_2('#skF_3', '#skF_2') | ~v3_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_48, c_6725])).
% 8.81/3.06  tff(c_6743, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_6562, c_6736])).
% 8.81/3.06  tff(c_7356, plain, (![B_341, A_342]: (v1_zfmisc_1(B_341) | ~v2_tex_2(B_341, A_342) | ~m1_subset_1(B_341, k1_zfmisc_1(u1_struct_0(A_342))) | v1_xboole_0(B_341) | ~l1_pre_topc(A_342) | ~v2_tdlat_3(A_342) | ~v2_pre_topc(A_342) | v2_struct_0(A_342))), inference(cnfTransformation, [status(thm)], [f_128])).
% 8.81/3.06  tff(c_7387, plain, (v1_zfmisc_1('#skF_3') | ~v2_tex_2('#skF_3', '#skF_2') | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_7356])).
% 8.81/3.06  tff(c_7401, plain, (v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_6743, c_7387])).
% 8.81/3.06  tff(c_7403, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_50, c_6561, c_7401])).
% 8.81/3.06  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.81/3.06  
% 8.81/3.06  Inference rules
% 8.81/3.06  ----------------------
% 8.81/3.06  #Ref     : 4
% 8.81/3.06  #Sup     : 1723
% 8.81/3.06  #Fact    : 18
% 8.81/3.06  #Define  : 0
% 8.81/3.06  #Split   : 16
% 8.81/3.06  #Chain   : 0
% 8.81/3.06  #Close   : 0
% 8.81/3.06  
% 8.81/3.06  Ordering : KBO
% 8.81/3.06  
% 8.81/3.06  Simplification rules
% 8.81/3.06  ----------------------
% 8.81/3.06  #Subsume      : 828
% 8.81/3.06  #Demod        : 466
% 8.81/3.06  #Tautology    : 309
% 8.81/3.06  #SimpNegUnit  : 143
% 8.81/3.06  #BackRed      : 7
% 8.81/3.06  
% 8.81/3.06  #Partial instantiations: 0
% 8.81/3.06  #Strategies tried      : 1
% 8.81/3.06  
% 8.81/3.06  Timing (in seconds)
% 8.81/3.06  ----------------------
% 8.81/3.07  Preprocessing        : 0.33
% 8.81/3.07  Parsing              : 0.18
% 8.81/3.07  CNF conversion       : 0.02
% 8.81/3.07  Main loop            : 1.90
% 8.81/3.07  Inferencing          : 0.48
% 8.81/3.07  Reduction            : 0.48
% 8.81/3.07  Demodulation         : 0.30
% 8.81/3.07  BG Simplification    : 0.05
% 8.81/3.07  Subsumption          : 0.80
% 8.81/3.07  Abstraction          : 0.08
% 8.81/3.07  MUC search           : 0.00
% 8.81/3.07  Cooper               : 0.00
% 8.81/3.07  Total                : 2.26
% 8.81/3.07  Index Insertion      : 0.00
% 8.81/3.07  Index Deletion       : 0.00
% 8.81/3.07  Index Matching       : 0.00
% 8.81/3.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
