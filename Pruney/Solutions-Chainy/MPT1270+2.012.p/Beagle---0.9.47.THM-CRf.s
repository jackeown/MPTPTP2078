%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:56 EST 2020

% Result     : Theorem 6.57s
% Output     : CNFRefutation 6.93s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 250 expanded)
%              Number of leaves         :   36 (  97 expanded)
%              Depth                    :   15
%              Number of atoms          :  211 ( 471 expanded)
%              Number of equality atoms :   58 (  97 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_122,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> r1_tarski(B,k2_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_59,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_112,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_103,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_xboole_0(k1_tops_1(A,B),k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_tops_1)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_46,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_44,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_3505,plain,(
    ! [B_320,A_321] :
      ( r1_tarski(B_320,k2_pre_topc(A_321,B_320))
      | ~ m1_subset_1(B_320,k1_zfmisc_1(u1_struct_0(A_321)))
      | ~ l1_pre_topc(A_321) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_3510,plain,
    ( r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_3505])).

tff(c_3517,plain,(
    r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_3510])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(A_19,k1_zfmisc_1(B_20))
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_3018,plain,(
    ! [A_272,B_273] :
      ( k4_xboole_0(A_272,B_273) = k3_subset_1(A_272,B_273)
      | ~ m1_subset_1(B_273,k1_zfmisc_1(A_272)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_3122,plain,(
    ! [B_280,A_281] :
      ( k4_xboole_0(B_280,A_281) = k3_subset_1(B_280,A_281)
      | ~ r1_tarski(A_281,B_280) ) ),
    inference(resolution,[status(thm)],[c_26,c_3018])).

tff(c_3137,plain,(
    ! [B_282] : k4_xboole_0(B_282,B_282) = k3_subset_1(B_282,B_282) ),
    inference(resolution,[status(thm)],[c_6,c_3122])).

tff(c_2938,plain,(
    ! [A_257,C_258,B_259] :
      ( r1_xboole_0(A_257,k4_xboole_0(C_258,B_259))
      | ~ r1_tarski(A_257,B_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( k4_xboole_0(A_6,B_7) = A_6
      | ~ r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2942,plain,(
    ! [A_257,C_258,B_259] :
      ( k4_xboole_0(A_257,k4_xboole_0(C_258,B_259)) = A_257
      | ~ r1_tarski(A_257,B_259) ) ),
    inference(resolution,[status(thm)],[c_2938,c_10])).

tff(c_3147,plain,(
    ! [A_257,B_282] :
      ( k4_xboole_0(A_257,k3_subset_1(B_282,B_282)) = A_257
      | ~ r1_tarski(A_257,B_282) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3137,c_2942])).

tff(c_22,plain,(
    ! [A_18] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_64,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(A_48,B_49)
      | ~ m1_subset_1(A_48,k1_zfmisc_1(B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_72,plain,(
    ! [A_18] : r1_tarski(k1_xboole_0,A_18) ),
    inference(resolution,[status(thm)],[c_22,c_64])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( r1_xboole_0(A_6,B_7)
      | k4_xboole_0(A_6,B_7) != A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2972,plain,(
    ! [A_263,C_264,B_265] :
      ( r1_xboole_0(A_263,C_264)
      | ~ r1_xboole_0(B_265,C_264)
      | ~ r1_tarski(A_263,B_265) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3270,plain,(
    ! [A_299,B_300,A_301] :
      ( r1_xboole_0(A_299,B_300)
      | ~ r1_tarski(A_299,A_301)
      | k4_xboole_0(A_301,B_300) != A_301 ) ),
    inference(resolution,[status(thm)],[c_12,c_2972])).

tff(c_3280,plain,(
    ! [B_302,A_303] :
      ( r1_xboole_0(k1_xboole_0,B_302)
      | k4_xboole_0(A_303,B_302) != A_303 ) ),
    inference(resolution,[status(thm)],[c_72,c_3270])).

tff(c_3731,plain,(
    ! [C_334,B_335,A_336] :
      ( r1_xboole_0(k1_xboole_0,k4_xboole_0(C_334,B_335))
      | ~ r1_tarski(A_336,B_335) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2942,c_3280])).

tff(c_3780,plain,(
    ! [C_339,B_340] : r1_xboole_0(k1_xboole_0,k4_xboole_0(C_339,B_340)) ),
    inference(resolution,[status(thm)],[c_6,c_3731])).

tff(c_3822,plain,(
    ! [A_342,B_343] :
      ( r1_xboole_0(k1_xboole_0,A_342)
      | ~ r1_tarski(A_342,B_343) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3147,c_3780])).

tff(c_3874,plain,(
    ! [B_346] : r1_xboole_0(k1_xboole_0,B_346) ),
    inference(resolution,[status(thm)],[c_6,c_3822])).

tff(c_3892,plain,(
    ! [B_347] : k4_xboole_0(k1_xboole_0,B_347) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3874,c_10])).

tff(c_14,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_xboole_0(A_8,k4_xboole_0(C_10,B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4065,plain,(
    ! [A_357,B_358] :
      ( r1_xboole_0(A_357,k1_xboole_0)
      | ~ r1_tarski(A_357,B_358) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3892,c_14])).

tff(c_4093,plain,(
    ! [B_359] : r1_xboole_0(B_359,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_4065])).

tff(c_4101,plain,(
    ! [B_359] : k4_xboole_0(B_359,k1_xboole_0) = B_359 ),
    inference(resolution,[status(thm)],[c_4093,c_10])).

tff(c_3992,plain,(
    ! [A_350,B_351] :
      ( m1_subset_1(k2_pre_topc(A_350,B_351),k1_zfmisc_1(u1_struct_0(A_350)))
      | ~ m1_subset_1(B_351,k1_zfmisc_1(u1_struct_0(A_350)))
      | ~ l1_pre_topc(A_350) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_20,plain,(
    ! [A_15,B_16,C_17] :
      ( k7_subset_1(A_15,B_16,C_17) = k4_xboole_0(B_16,C_17)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6858,plain,(
    ! [A_527,B_528,C_529] :
      ( k7_subset_1(u1_struct_0(A_527),k2_pre_topc(A_527,B_528),C_529) = k4_xboole_0(k2_pre_topc(A_527,B_528),C_529)
      | ~ m1_subset_1(B_528,k1_zfmisc_1(u1_struct_0(A_527)))
      | ~ l1_pre_topc(A_527) ) ),
    inference(resolution,[status(thm)],[c_3992,c_20])).

tff(c_6865,plain,(
    ! [C_529] :
      ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_529) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_529)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_44,c_6858])).

tff(c_6884,plain,(
    ! [C_531] : k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_531) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_531) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_6865])).

tff(c_48,plain,
    ( ~ r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_74,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_882,plain,(
    ! [B_135,A_136] :
      ( v2_tops_1(B_135,A_136)
      | k1_tops_1(A_136,B_135) != k1_xboole_0
      | ~ m1_subset_1(B_135,k1_zfmisc_1(u1_struct_0(A_136)))
      | ~ l1_pre_topc(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_889,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_882])).

tff(c_897,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_889])).

tff(c_898,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_897])).

tff(c_720,plain,(
    ! [A_123,B_124] :
      ( r1_tarski(k1_tops_1(A_123,B_124),B_124)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_pre_topc(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_725,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_720])).

tff(c_732,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_725])).

tff(c_163,plain,(
    ! [A_68,B_69] :
      ( k4_xboole_0(A_68,B_69) = k3_subset_1(A_68,B_69)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_267,plain,(
    ! [B_76,A_77] :
      ( k4_xboole_0(B_76,A_77) = k3_subset_1(B_76,A_77)
      | ~ r1_tarski(A_77,B_76) ) ),
    inference(resolution,[status(thm)],[c_26,c_163])).

tff(c_286,plain,(
    ! [B_78] : k4_xboole_0(B_78,B_78) = k3_subset_1(B_78,B_78) ),
    inference(resolution,[status(thm)],[c_6,c_267])).

tff(c_80,plain,(
    ! [A_53,C_54,B_55] :
      ( r1_xboole_0(A_53,k4_xboole_0(C_54,B_55))
      | ~ r1_tarski(A_53,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_84,plain,(
    ! [A_53,C_54,B_55] :
      ( k4_xboole_0(A_53,k4_xboole_0(C_54,B_55)) = A_53
      | ~ r1_tarski(A_53,B_55) ) ),
    inference(resolution,[status(thm)],[c_80,c_10])).

tff(c_296,plain,(
    ! [A_53,B_78] :
      ( k4_xboole_0(A_53,k3_subset_1(B_78,B_78)) = A_53
      | ~ r1_tarski(A_53,B_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_84])).

tff(c_102,plain,(
    ! [A_58,C_59,B_60] :
      ( r1_xboole_0(A_58,C_59)
      | ~ r1_xboole_0(B_60,C_59)
      | ~ r1_tarski(A_58,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_419,plain,(
    ! [A_95,B_96,A_97] :
      ( r1_xboole_0(A_95,B_96)
      | ~ r1_tarski(A_95,A_97)
      | k4_xboole_0(A_97,B_96) != A_97 ) ),
    inference(resolution,[status(thm)],[c_12,c_102])).

tff(c_432,plain,(
    ! [B_98,A_99] :
      ( r1_xboole_0(k1_xboole_0,B_98)
      | k4_xboole_0(A_99,B_98) != A_99 ) ),
    inference(resolution,[status(thm)],[c_72,c_419])).

tff(c_859,plain,(
    ! [C_132,B_133,A_134] :
      ( r1_xboole_0(k1_xboole_0,k4_xboole_0(C_132,B_133))
      | ~ r1_tarski(A_134,B_133) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_432])).

tff(c_916,plain,(
    ! [C_138,B_139] : r1_xboole_0(k1_xboole_0,k4_xboole_0(C_138,B_139)) ),
    inference(resolution,[status(thm)],[c_6,c_859])).

tff(c_973,plain,(
    ! [A_142,B_143] :
      ( r1_xboole_0(k1_xboole_0,A_142)
      | ~ r1_tarski(A_142,B_143) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_296,c_916])).

tff(c_1029,plain,(
    ! [B_146] : r1_xboole_0(k1_xboole_0,B_146) ),
    inference(resolution,[status(thm)],[c_6,c_973])).

tff(c_1041,plain,(
    ! [B_147] : k4_xboole_0(k1_xboole_0,B_147) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1029,c_10])).

tff(c_1203,plain,(
    ! [A_156,B_157] :
      ( r1_xboole_0(A_156,k1_xboole_0)
      | ~ r1_tarski(A_156,B_157) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1041,c_14])).

tff(c_1235,plain,(
    ! [B_158] : r1_xboole_0(B_158,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_1203])).

tff(c_1243,plain,(
    ! [B_158] : k4_xboole_0(B_158,k1_xboole_0) = B_158 ),
    inference(resolution,[status(thm)],[c_1235,c_10])).

tff(c_175,plain,(
    ! [A_18] : k4_xboole_0(A_18,k1_xboole_0) = k3_subset_1(A_18,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_22,c_163])).

tff(c_1263,plain,(
    ! [A_18] : k3_subset_1(A_18,k1_xboole_0) = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1243,c_175])).

tff(c_142,plain,(
    ! [A_65,B_66] :
      ( k3_subset_1(A_65,k3_subset_1(A_65,B_66)) = B_66
      | ~ m1_subset_1(B_66,k1_zfmisc_1(A_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_151,plain,(
    ! [A_18] : k3_subset_1(A_18,k3_subset_1(A_18,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_142])).

tff(c_1322,plain,(
    ! [A_18] : k3_subset_1(A_18,A_18) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1263,c_151])).

tff(c_1182,plain,(
    ! [A_152,B_153] :
      ( r1_xboole_0(k1_tops_1(A_152,B_153),k2_tops_1(A_152,B_153))
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0(A_152)))
      | ~ l1_pre_topc(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2839,plain,(
    ! [A_253,B_254] :
      ( k4_xboole_0(k1_tops_1(A_253,B_254),k2_tops_1(A_253,B_254)) = k1_tops_1(A_253,B_254)
      | ~ m1_subset_1(B_254,k1_zfmisc_1(u1_struct_0(A_253)))
      | ~ l1_pre_topc(A_253) ) ),
    inference(resolution,[status(thm)],[c_1182,c_10])).

tff(c_2846,plain,
    ( k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_2839])).

tff(c_2854,plain,(
    k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2846])).

tff(c_54,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_85,plain,(
    r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_54])).

tff(c_1691,plain,(
    ! [A_188,C_189,B_190,A_191] :
      ( r1_xboole_0(A_188,k4_xboole_0(C_189,B_190))
      | ~ r1_tarski(A_188,A_191)
      | ~ r1_tarski(A_191,B_190) ) ),
    inference(resolution,[status(thm)],[c_14,c_102])).

tff(c_1717,plain,(
    ! [C_189,B_190] :
      ( r1_xboole_0('#skF_2',k4_xboole_0(C_189,B_190))
      | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),B_190) ) ),
    inference(resolution,[status(thm)],[c_85,c_1691])).

tff(c_2862,plain,
    ( r1_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2'))
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2854,c_1717])).

tff(c_2881,plain,(
    r1_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2862])).

tff(c_2893,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_2881,c_10])).

tff(c_173,plain,(
    ! [B_20,A_19] :
      ( k4_xboole_0(B_20,A_19) = k3_subset_1(B_20,A_19)
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(resolution,[status(thm)],[c_26,c_163])).

tff(c_742,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_732,c_173])).

tff(c_2894,plain,(
    k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2893,c_742])).

tff(c_149,plain,(
    ! [B_20,A_19] :
      ( k3_subset_1(B_20,k3_subset_1(B_20,A_19)) = A_19
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(resolution,[status(thm)],[c_26,c_142])).

tff(c_2924,plain,
    ( k3_subset_1('#skF_2','#skF_2') = k1_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2894,c_149])).

tff(c_2928,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_732,c_1322,c_2924])).

tff(c_2930,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_898,c_2928])).

tff(c_2932,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_3842,plain,(
    ! [A_344,B_345] :
      ( k1_tops_1(A_344,B_345) = k1_xboole_0
      | ~ v2_tops_1(B_345,A_344)
      | ~ m1_subset_1(B_345,k1_zfmisc_1(u1_struct_0(A_344)))
      | ~ l1_pre_topc(A_344) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_3849,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_3842])).

tff(c_3857,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2932,c_3849])).

tff(c_4216,plain,(
    ! [A_363,B_364] :
      ( k7_subset_1(u1_struct_0(A_363),k2_pre_topc(A_363,B_364),k1_tops_1(A_363,B_364)) = k2_tops_1(A_363,B_364)
      | ~ m1_subset_1(B_364,k1_zfmisc_1(u1_struct_0(A_363)))
      | ~ l1_pre_topc(A_363) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_4225,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k1_xboole_0) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3857,c_4216])).

tff(c_4232,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k1_xboole_0) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_4225])).

tff(c_6890,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k1_xboole_0) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6884,c_4232])).

tff(c_6906,plain,(
    k2_tops_1('#skF_1','#skF_2') = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4101,c_6890])).

tff(c_2931,plain,(
    ~ r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_6914,plain,(
    ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6906,c_2931])).

tff(c_6917,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3517,c_6914])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:58:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.57/2.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.57/2.43  
% 6.57/2.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.57/2.43  %$ v2_tops_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 6.57/2.43  
% 6.57/2.43  %Foreground sorts:
% 6.57/2.43  
% 6.57/2.43  
% 6.57/2.43  %Background operators:
% 6.57/2.43  
% 6.57/2.43  
% 6.57/2.43  %Foreground operators:
% 6.57/2.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.57/2.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.57/2.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.57/2.43  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 6.57/2.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.57/2.43  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 6.57/2.43  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.57/2.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.57/2.43  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 6.57/2.43  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 6.57/2.43  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.57/2.43  tff('#skF_2', type, '#skF_2': $i).
% 6.57/2.43  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 6.57/2.43  tff('#skF_1', type, '#skF_1': $i).
% 6.57/2.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.57/2.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.57/2.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.57/2.43  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.57/2.43  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 6.57/2.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.57/2.43  
% 6.93/2.45  tff(f_122, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tops_1)).
% 6.93/2.45  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 6.93/2.45  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.93/2.45  tff(f_63, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.93/2.45  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 6.93/2.45  tff(f_45, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 6.93/2.45  tff(f_41, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 6.93/2.45  tff(f_59, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 6.93/2.45  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 6.93/2.45  tff(f_75, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 6.93/2.45  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 6.93/2.45  tff(f_112, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 6.93/2.45  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 6.93/2.45  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 6.93/2.45  tff(f_103, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_xboole_0(k1_tops_1(A, B), k2_tops_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_tops_1)).
% 6.93/2.45  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 6.93/2.45  tff(c_46, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.93/2.45  tff(c_44, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.93/2.45  tff(c_3505, plain, (![B_320, A_321]: (r1_tarski(B_320, k2_pre_topc(A_321, B_320)) | ~m1_subset_1(B_320, k1_zfmisc_1(u1_struct_0(A_321))) | ~l1_pre_topc(A_321))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.93/2.45  tff(c_3510, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_3505])).
% 6.93/2.45  tff(c_3517, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_3510])).
% 6.93/2.45  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.93/2.45  tff(c_26, plain, (![A_19, B_20]: (m1_subset_1(A_19, k1_zfmisc_1(B_20)) | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.93/2.45  tff(c_3018, plain, (![A_272, B_273]: (k4_xboole_0(A_272, B_273)=k3_subset_1(A_272, B_273) | ~m1_subset_1(B_273, k1_zfmisc_1(A_272)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.93/2.45  tff(c_3122, plain, (![B_280, A_281]: (k4_xboole_0(B_280, A_281)=k3_subset_1(B_280, A_281) | ~r1_tarski(A_281, B_280))), inference(resolution, [status(thm)], [c_26, c_3018])).
% 6.93/2.45  tff(c_3137, plain, (![B_282]: (k4_xboole_0(B_282, B_282)=k3_subset_1(B_282, B_282))), inference(resolution, [status(thm)], [c_6, c_3122])).
% 6.93/2.45  tff(c_2938, plain, (![A_257, C_258, B_259]: (r1_xboole_0(A_257, k4_xboole_0(C_258, B_259)) | ~r1_tarski(A_257, B_259))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.93/2.45  tff(c_10, plain, (![A_6, B_7]: (k4_xboole_0(A_6, B_7)=A_6 | ~r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.93/2.45  tff(c_2942, plain, (![A_257, C_258, B_259]: (k4_xboole_0(A_257, k4_xboole_0(C_258, B_259))=A_257 | ~r1_tarski(A_257, B_259))), inference(resolution, [status(thm)], [c_2938, c_10])).
% 6.93/2.45  tff(c_3147, plain, (![A_257, B_282]: (k4_xboole_0(A_257, k3_subset_1(B_282, B_282))=A_257 | ~r1_tarski(A_257, B_282))), inference(superposition, [status(thm), theory('equality')], [c_3137, c_2942])).
% 6.93/2.45  tff(c_22, plain, (![A_18]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.93/2.45  tff(c_64, plain, (![A_48, B_49]: (r1_tarski(A_48, B_49) | ~m1_subset_1(A_48, k1_zfmisc_1(B_49)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.93/2.45  tff(c_72, plain, (![A_18]: (r1_tarski(k1_xboole_0, A_18))), inference(resolution, [status(thm)], [c_22, c_64])).
% 6.93/2.45  tff(c_12, plain, (![A_6, B_7]: (r1_xboole_0(A_6, B_7) | k4_xboole_0(A_6, B_7)!=A_6)), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.93/2.45  tff(c_2972, plain, (![A_263, C_264, B_265]: (r1_xboole_0(A_263, C_264) | ~r1_xboole_0(B_265, C_264) | ~r1_tarski(A_263, B_265))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.93/2.45  tff(c_3270, plain, (![A_299, B_300, A_301]: (r1_xboole_0(A_299, B_300) | ~r1_tarski(A_299, A_301) | k4_xboole_0(A_301, B_300)!=A_301)), inference(resolution, [status(thm)], [c_12, c_2972])).
% 6.93/2.45  tff(c_3280, plain, (![B_302, A_303]: (r1_xboole_0(k1_xboole_0, B_302) | k4_xboole_0(A_303, B_302)!=A_303)), inference(resolution, [status(thm)], [c_72, c_3270])).
% 6.93/2.45  tff(c_3731, plain, (![C_334, B_335, A_336]: (r1_xboole_0(k1_xboole_0, k4_xboole_0(C_334, B_335)) | ~r1_tarski(A_336, B_335))), inference(superposition, [status(thm), theory('equality')], [c_2942, c_3280])).
% 6.93/2.45  tff(c_3780, plain, (![C_339, B_340]: (r1_xboole_0(k1_xboole_0, k4_xboole_0(C_339, B_340)))), inference(resolution, [status(thm)], [c_6, c_3731])).
% 6.93/2.45  tff(c_3822, plain, (![A_342, B_343]: (r1_xboole_0(k1_xboole_0, A_342) | ~r1_tarski(A_342, B_343))), inference(superposition, [status(thm), theory('equality')], [c_3147, c_3780])).
% 6.93/2.45  tff(c_3874, plain, (![B_346]: (r1_xboole_0(k1_xboole_0, B_346))), inference(resolution, [status(thm)], [c_6, c_3822])).
% 6.93/2.45  tff(c_3892, plain, (![B_347]: (k4_xboole_0(k1_xboole_0, B_347)=k1_xboole_0)), inference(resolution, [status(thm)], [c_3874, c_10])).
% 6.93/2.45  tff(c_14, plain, (![A_8, C_10, B_9]: (r1_xboole_0(A_8, k4_xboole_0(C_10, B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.93/2.45  tff(c_4065, plain, (![A_357, B_358]: (r1_xboole_0(A_357, k1_xboole_0) | ~r1_tarski(A_357, B_358))), inference(superposition, [status(thm), theory('equality')], [c_3892, c_14])).
% 6.93/2.45  tff(c_4093, plain, (![B_359]: (r1_xboole_0(B_359, k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_4065])).
% 6.93/2.45  tff(c_4101, plain, (![B_359]: (k4_xboole_0(B_359, k1_xboole_0)=B_359)), inference(resolution, [status(thm)], [c_4093, c_10])).
% 6.93/2.45  tff(c_3992, plain, (![A_350, B_351]: (m1_subset_1(k2_pre_topc(A_350, B_351), k1_zfmisc_1(u1_struct_0(A_350))) | ~m1_subset_1(B_351, k1_zfmisc_1(u1_struct_0(A_350))) | ~l1_pre_topc(A_350))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.93/2.45  tff(c_20, plain, (![A_15, B_16, C_17]: (k7_subset_1(A_15, B_16, C_17)=k4_xboole_0(B_16, C_17) | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.93/2.45  tff(c_6858, plain, (![A_527, B_528, C_529]: (k7_subset_1(u1_struct_0(A_527), k2_pre_topc(A_527, B_528), C_529)=k4_xboole_0(k2_pre_topc(A_527, B_528), C_529) | ~m1_subset_1(B_528, k1_zfmisc_1(u1_struct_0(A_527))) | ~l1_pre_topc(A_527))), inference(resolution, [status(thm)], [c_3992, c_20])).
% 6.93/2.45  tff(c_6865, plain, (![C_529]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_529)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_529) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_6858])).
% 6.93/2.45  tff(c_6884, plain, (![C_531]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_531)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_531))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_6865])).
% 6.93/2.45  tff(c_48, plain, (~r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.93/2.45  tff(c_74, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_48])).
% 6.93/2.45  tff(c_882, plain, (![B_135, A_136]: (v2_tops_1(B_135, A_136) | k1_tops_1(A_136, B_135)!=k1_xboole_0 | ~m1_subset_1(B_135, k1_zfmisc_1(u1_struct_0(A_136))) | ~l1_pre_topc(A_136))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.93/2.45  tff(c_889, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_882])).
% 6.93/2.45  tff(c_897, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_46, c_889])).
% 6.93/2.45  tff(c_898, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_74, c_897])).
% 6.93/2.45  tff(c_720, plain, (![A_123, B_124]: (r1_tarski(k1_tops_1(A_123, B_124), B_124) | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0(A_123))) | ~l1_pre_topc(A_123))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.93/2.45  tff(c_725, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_720])).
% 6.93/2.45  tff(c_732, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_725])).
% 6.93/2.45  tff(c_163, plain, (![A_68, B_69]: (k4_xboole_0(A_68, B_69)=k3_subset_1(A_68, B_69) | ~m1_subset_1(B_69, k1_zfmisc_1(A_68)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.93/2.45  tff(c_267, plain, (![B_76, A_77]: (k4_xboole_0(B_76, A_77)=k3_subset_1(B_76, A_77) | ~r1_tarski(A_77, B_76))), inference(resolution, [status(thm)], [c_26, c_163])).
% 6.93/2.45  tff(c_286, plain, (![B_78]: (k4_xboole_0(B_78, B_78)=k3_subset_1(B_78, B_78))), inference(resolution, [status(thm)], [c_6, c_267])).
% 6.93/2.45  tff(c_80, plain, (![A_53, C_54, B_55]: (r1_xboole_0(A_53, k4_xboole_0(C_54, B_55)) | ~r1_tarski(A_53, B_55))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.93/2.45  tff(c_84, plain, (![A_53, C_54, B_55]: (k4_xboole_0(A_53, k4_xboole_0(C_54, B_55))=A_53 | ~r1_tarski(A_53, B_55))), inference(resolution, [status(thm)], [c_80, c_10])).
% 6.93/2.45  tff(c_296, plain, (![A_53, B_78]: (k4_xboole_0(A_53, k3_subset_1(B_78, B_78))=A_53 | ~r1_tarski(A_53, B_78))), inference(superposition, [status(thm), theory('equality')], [c_286, c_84])).
% 6.93/2.45  tff(c_102, plain, (![A_58, C_59, B_60]: (r1_xboole_0(A_58, C_59) | ~r1_xboole_0(B_60, C_59) | ~r1_tarski(A_58, B_60))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.93/2.45  tff(c_419, plain, (![A_95, B_96, A_97]: (r1_xboole_0(A_95, B_96) | ~r1_tarski(A_95, A_97) | k4_xboole_0(A_97, B_96)!=A_97)), inference(resolution, [status(thm)], [c_12, c_102])).
% 6.93/2.45  tff(c_432, plain, (![B_98, A_99]: (r1_xboole_0(k1_xboole_0, B_98) | k4_xboole_0(A_99, B_98)!=A_99)), inference(resolution, [status(thm)], [c_72, c_419])).
% 6.93/2.45  tff(c_859, plain, (![C_132, B_133, A_134]: (r1_xboole_0(k1_xboole_0, k4_xboole_0(C_132, B_133)) | ~r1_tarski(A_134, B_133))), inference(superposition, [status(thm), theory('equality')], [c_84, c_432])).
% 6.93/2.45  tff(c_916, plain, (![C_138, B_139]: (r1_xboole_0(k1_xboole_0, k4_xboole_0(C_138, B_139)))), inference(resolution, [status(thm)], [c_6, c_859])).
% 6.93/2.45  tff(c_973, plain, (![A_142, B_143]: (r1_xboole_0(k1_xboole_0, A_142) | ~r1_tarski(A_142, B_143))), inference(superposition, [status(thm), theory('equality')], [c_296, c_916])).
% 6.93/2.45  tff(c_1029, plain, (![B_146]: (r1_xboole_0(k1_xboole_0, B_146))), inference(resolution, [status(thm)], [c_6, c_973])).
% 6.93/2.45  tff(c_1041, plain, (![B_147]: (k4_xboole_0(k1_xboole_0, B_147)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1029, c_10])).
% 6.93/2.45  tff(c_1203, plain, (![A_156, B_157]: (r1_xboole_0(A_156, k1_xboole_0) | ~r1_tarski(A_156, B_157))), inference(superposition, [status(thm), theory('equality')], [c_1041, c_14])).
% 6.93/2.45  tff(c_1235, plain, (![B_158]: (r1_xboole_0(B_158, k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_1203])).
% 6.93/2.45  tff(c_1243, plain, (![B_158]: (k4_xboole_0(B_158, k1_xboole_0)=B_158)), inference(resolution, [status(thm)], [c_1235, c_10])).
% 6.93/2.45  tff(c_175, plain, (![A_18]: (k4_xboole_0(A_18, k1_xboole_0)=k3_subset_1(A_18, k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_163])).
% 6.93/2.45  tff(c_1263, plain, (![A_18]: (k3_subset_1(A_18, k1_xboole_0)=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_1243, c_175])).
% 6.93/2.45  tff(c_142, plain, (![A_65, B_66]: (k3_subset_1(A_65, k3_subset_1(A_65, B_66))=B_66 | ~m1_subset_1(B_66, k1_zfmisc_1(A_65)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.93/2.45  tff(c_151, plain, (![A_18]: (k3_subset_1(A_18, k3_subset_1(A_18, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_142])).
% 6.93/2.45  tff(c_1322, plain, (![A_18]: (k3_subset_1(A_18, A_18)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1263, c_151])).
% 6.93/2.45  tff(c_1182, plain, (![A_152, B_153]: (r1_xboole_0(k1_tops_1(A_152, B_153), k2_tops_1(A_152, B_153)) | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0(A_152))) | ~l1_pre_topc(A_152))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.93/2.45  tff(c_2839, plain, (![A_253, B_254]: (k4_xboole_0(k1_tops_1(A_253, B_254), k2_tops_1(A_253, B_254))=k1_tops_1(A_253, B_254) | ~m1_subset_1(B_254, k1_zfmisc_1(u1_struct_0(A_253))) | ~l1_pre_topc(A_253))), inference(resolution, [status(thm)], [c_1182, c_10])).
% 6.93/2.45  tff(c_2846, plain, (k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_2839])).
% 6.93/2.45  tff(c_2854, plain, (k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_2846])).
% 6.93/2.45  tff(c_54, plain, (v2_tops_1('#skF_2', '#skF_1') | r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.93/2.45  tff(c_85, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_74, c_54])).
% 6.93/2.45  tff(c_1691, plain, (![A_188, C_189, B_190, A_191]: (r1_xboole_0(A_188, k4_xboole_0(C_189, B_190)) | ~r1_tarski(A_188, A_191) | ~r1_tarski(A_191, B_190))), inference(resolution, [status(thm)], [c_14, c_102])).
% 6.93/2.45  tff(c_1717, plain, (![C_189, B_190]: (r1_xboole_0('#skF_2', k4_xboole_0(C_189, B_190)) | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), B_190))), inference(resolution, [status(thm)], [c_85, c_1691])).
% 6.93/2.45  tff(c_2862, plain, (r1_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2854, c_1717])).
% 6.93/2.45  tff(c_2881, plain, (r1_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_2862])).
% 6.93/2.45  tff(c_2893, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_2881, c_10])).
% 6.93/2.45  tff(c_173, plain, (![B_20, A_19]: (k4_xboole_0(B_20, A_19)=k3_subset_1(B_20, A_19) | ~r1_tarski(A_19, B_20))), inference(resolution, [status(thm)], [c_26, c_163])).
% 6.93/2.45  tff(c_742, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_732, c_173])).
% 6.93/2.45  tff(c_2894, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2893, c_742])).
% 6.93/2.45  tff(c_149, plain, (![B_20, A_19]: (k3_subset_1(B_20, k3_subset_1(B_20, A_19))=A_19 | ~r1_tarski(A_19, B_20))), inference(resolution, [status(thm)], [c_26, c_142])).
% 6.93/2.45  tff(c_2924, plain, (k3_subset_1('#skF_2', '#skF_2')=k1_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2894, c_149])).
% 6.93/2.45  tff(c_2928, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_732, c_1322, c_2924])).
% 6.93/2.45  tff(c_2930, plain, $false, inference(negUnitSimplification, [status(thm)], [c_898, c_2928])).
% 6.93/2.45  tff(c_2932, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_48])).
% 6.93/2.45  tff(c_3842, plain, (![A_344, B_345]: (k1_tops_1(A_344, B_345)=k1_xboole_0 | ~v2_tops_1(B_345, A_344) | ~m1_subset_1(B_345, k1_zfmisc_1(u1_struct_0(A_344))) | ~l1_pre_topc(A_344))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.93/2.45  tff(c_3849, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_3842])).
% 6.93/2.45  tff(c_3857, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_46, c_2932, c_3849])).
% 6.93/2.45  tff(c_4216, plain, (![A_363, B_364]: (k7_subset_1(u1_struct_0(A_363), k2_pre_topc(A_363, B_364), k1_tops_1(A_363, B_364))=k2_tops_1(A_363, B_364) | ~m1_subset_1(B_364, k1_zfmisc_1(u1_struct_0(A_363))) | ~l1_pre_topc(A_363))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.93/2.45  tff(c_4225, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k1_xboole_0)=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3857, c_4216])).
% 6.93/2.45  tff(c_4232, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k1_xboole_0)=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_4225])).
% 6.93/2.45  tff(c_6890, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k1_xboole_0)=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6884, c_4232])).
% 6.93/2.45  tff(c_6906, plain, (k2_tops_1('#skF_1', '#skF_2')=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4101, c_6890])).
% 6.93/2.45  tff(c_2931, plain, (~r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_48])).
% 6.93/2.45  tff(c_6914, plain, (~r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_6906, c_2931])).
% 6.93/2.45  tff(c_6917, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3517, c_6914])).
% 6.93/2.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.93/2.45  
% 6.93/2.45  Inference rules
% 6.93/2.45  ----------------------
% 6.93/2.45  #Ref     : 0
% 6.93/2.45  #Sup     : 1718
% 6.93/2.45  #Fact    : 0
% 6.93/2.45  #Define  : 0
% 6.93/2.45  #Split   : 32
% 6.93/2.45  #Chain   : 0
% 6.93/2.45  #Close   : 0
% 6.93/2.45  
% 6.93/2.45  Ordering : KBO
% 6.93/2.45  
% 6.93/2.45  Simplification rules
% 6.93/2.45  ----------------------
% 6.93/2.45  #Subsume      : 357
% 6.93/2.45  #Demod        : 619
% 6.93/2.45  #Tautology    : 660
% 6.93/2.45  #SimpNegUnit  : 12
% 6.93/2.45  #BackRed      : 20
% 6.93/2.45  
% 6.93/2.45  #Partial instantiations: 0
% 6.93/2.45  #Strategies tried      : 1
% 6.93/2.45  
% 6.93/2.45  Timing (in seconds)
% 6.93/2.45  ----------------------
% 6.93/2.46  Preprocessing        : 0.34
% 6.93/2.46  Parsing              : 0.19
% 6.93/2.46  CNF conversion       : 0.02
% 6.93/2.46  Main loop            : 1.27
% 6.93/2.46  Inferencing          : 0.42
% 6.93/2.46  Reduction            : 0.42
% 6.93/2.46  Demodulation         : 0.29
% 6.93/2.46  BG Simplification    : 0.05
% 6.93/2.46  Subsumption          : 0.28
% 6.93/2.46  Abstraction          : 0.05
% 6.93/2.46  MUC search           : 0.00
% 6.93/2.46  Cooper               : 0.00
% 6.93/2.46  Total                : 1.67
% 6.93/2.46  Index Insertion      : 0.00
% 6.93/2.46  Index Deletion       : 0.00
% 6.93/2.46  Index Matching       : 0.00
% 6.93/2.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
