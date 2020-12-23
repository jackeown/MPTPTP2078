%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1359+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:51 EST 2020

% Result     : Theorem 4.68s
% Output     : CNFRefutation 5.06s
% Verified   : 
% Statistics : Number of formulae       :  158 (1384 expanded)
%              Number of leaves         :   28 ( 453 expanded)
%              Depth                    :   18
%              Number of atoms          :  442 (7013 expanded)
%              Number of equality atoms :  129 (2035 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_2 > r1_tarski > m1_subset_1 > v3_finset_1 > v2_struct_0 > v2_pre_topc > v1_finset_1 > v1_compts_1 > l1_pre_topc > k6_setfam_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_1 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v2_tops_2,type,(
    v2_tops_2: ( $i * $i ) > $o )).

tff(v3_finset_1,type,(
    v3_finset_1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_compts_1,type,(
    v1_compts_1: $i > $o )).

tff(v1_finset_1,type,(
    v1_finset_1: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_107,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ( v1_compts_1(A)
        <=> ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ~ ( B != k1_xboole_0
                  & v2_tops_2(B,A)
                  & k6_setfam_1(u1_struct_0(A),B) = k1_xboole_0
                  & ! [C] :
                      ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
                     => ~ ( C != k1_xboole_0
                          & r1_tarski(C,B)
                          & v1_finset_1(C)
                          & k6_setfam_1(u1_struct_0(A),C) = k1_xboole_0 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_compts_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v3_finset_1(A)
    <=> ( A != k1_xboole_0
        & ! [B] :
            ~ ( B != k1_xboole_0
              & r1_tarski(B,A)
              & v1_finset_1(B)
              & k1_setfam_1(B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_finset_1)).

tff(f_63,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_compts_1(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ~ ( v3_finset_1(B)
                & v2_tops_2(B,A)
                & k6_setfam_1(u1_struct_0(A),B) = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_compts_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_44,plain,
    ( k1_xboole_0 != '#skF_4'
    | ~ v1_compts_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_109,plain,(
    ~ v1_compts_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_4,plain,(
    ~ v3_finset_1(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_34,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_32,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_18,plain,(
    ! [A_7] :
      ( k6_setfam_1(u1_struct_0(A_7),'#skF_2'(A_7)) = k1_xboole_0
      | v1_compts_1(A_7)
      | ~ l1_pre_topc(A_7)
      | ~ v2_pre_topc(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_20,plain,(
    ! [A_7] :
      ( v2_tops_2('#skF_2'(A_7),A_7)
      | v1_compts_1(A_7)
      | ~ l1_pre_topc(A_7)
      | ~ v2_pre_topc(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_24,plain,(
    ! [A_7] :
      ( m1_subset_1('#skF_2'(A_7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_7))))
      | v1_compts_1(A_7)
      | ~ l1_pre_topc(A_7)
      | ~ v2_pre_topc(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_72,plain,(
    ! [B_24] :
      ( v1_compts_1('#skF_3')
      | v1_finset_1('#skF_5'(B_24))
      | k6_setfam_1(u1_struct_0('#skF_3'),B_24) != k1_xboole_0
      | ~ v2_tops_2(B_24,'#skF_3')
      | k1_xboole_0 = B_24
      | ~ m1_subset_1(B_24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_182,plain,(
    ! [B_49] :
      ( v1_finset_1('#skF_5'(B_49))
      | k6_setfam_1(u1_struct_0('#skF_3'),B_49) != k1_xboole_0
      | ~ v2_tops_2(B_49,'#skF_3')
      | k1_xboole_0 = B_49
      | ~ m1_subset_1(B_49,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_72])).

tff(c_186,plain,
    ( v1_finset_1('#skF_5'('#skF_2'('#skF_3')))
    | k6_setfam_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3')) != k1_xboole_0
    | ~ v2_tops_2('#skF_2'('#skF_3'),'#skF_3')
    | '#skF_2'('#skF_3') = k1_xboole_0
    | v1_compts_1('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_182])).

tff(c_193,plain,
    ( v1_finset_1('#skF_5'('#skF_2'('#skF_3')))
    | k6_setfam_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3')) != k1_xboole_0
    | ~ v2_tops_2('#skF_2'('#skF_3'),'#skF_3')
    | '#skF_2'('#skF_3') = k1_xboole_0
    | v1_compts_1('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_186])).

tff(c_194,plain,
    ( v1_finset_1('#skF_5'('#skF_2'('#skF_3')))
    | k6_setfam_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3')) != k1_xboole_0
    | ~ v2_tops_2('#skF_2'('#skF_3'),'#skF_3')
    | '#skF_2'('#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_109,c_193])).

tff(c_265,plain,(
    ~ v2_tops_2('#skF_2'('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_194])).

tff(c_268,plain,
    ( v1_compts_1('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_265])).

tff(c_271,plain,
    ( v1_compts_1('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_268])).

tff(c_273,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_109,c_271])).

tff(c_274,plain,
    ( k6_setfam_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3')) != k1_xboole_0
    | '#skF_2'('#skF_3') = k1_xboole_0
    | v1_finset_1('#skF_5'('#skF_2'('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_194])).

tff(c_276,plain,(
    k6_setfam_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_274])).

tff(c_282,plain,
    ( v1_compts_1('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_276])).

tff(c_288,plain,
    ( v1_compts_1('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_282])).

tff(c_290,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_109,c_288])).

tff(c_291,plain,
    ( v1_finset_1('#skF_5'('#skF_2'('#skF_3')))
    | '#skF_2'('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_274])).

tff(c_328,plain,(
    '#skF_2'('#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_291])).

tff(c_22,plain,(
    ! [A_7] :
      ( v3_finset_1('#skF_2'(A_7))
      | v1_compts_1(A_7)
      | ~ l1_pre_topc(A_7)
      | ~ v2_pre_topc(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_350,plain,
    ( v3_finset_1(k1_xboole_0)
    | v1_compts_1('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_328,c_22])).

tff(c_369,plain,
    ( v3_finset_1(k1_xboole_0)
    | v1_compts_1('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_350])).

tff(c_371,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_109,c_4,c_369])).

tff(c_373,plain,(
    '#skF_2'('#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_291])).

tff(c_275,plain,(
    v2_tops_2('#skF_2'('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_194])).

tff(c_292,plain,(
    k6_setfam_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_274])).

tff(c_96,plain,(
    ! [B_24] :
      ( v1_compts_1('#skF_3')
      | '#skF_5'(B_24) != k1_xboole_0
      | k6_setfam_1(u1_struct_0('#skF_3'),B_24) != k1_xboole_0
      | ~ v2_tops_2(B_24,'#skF_3')
      | k1_xboole_0 = B_24
      | ~ m1_subset_1(B_24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_236,plain,(
    ! [B_53] :
      ( '#skF_5'(B_53) != k1_xboole_0
      | k6_setfam_1(u1_struct_0('#skF_3'),B_53) != k1_xboole_0
      | ~ v2_tops_2(B_53,'#skF_3')
      | k1_xboole_0 = B_53
      | ~ m1_subset_1(B_53,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_96])).

tff(c_240,plain,
    ( '#skF_5'('#skF_2'('#skF_3')) != k1_xboole_0
    | k6_setfam_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3')) != k1_xboole_0
    | ~ v2_tops_2('#skF_2'('#skF_3'),'#skF_3')
    | '#skF_2'('#skF_3') = k1_xboole_0
    | v1_compts_1('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_236])).

tff(c_247,plain,
    ( '#skF_5'('#skF_2'('#skF_3')) != k1_xboole_0
    | k6_setfam_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3')) != k1_xboole_0
    | ~ v2_tops_2('#skF_2'('#skF_3'),'#skF_3')
    | '#skF_2'('#skF_3') = k1_xboole_0
    | v1_compts_1('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_240])).

tff(c_248,plain,
    ( '#skF_5'('#skF_2'('#skF_3')) != k1_xboole_0
    | k6_setfam_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3')) != k1_xboole_0
    | ~ v2_tops_2('#skF_2'('#skF_3'),'#skF_3')
    | '#skF_2'('#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_109,c_247])).

tff(c_375,plain,
    ( '#skF_5'('#skF_2'('#skF_3')) != k1_xboole_0
    | '#skF_2'('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_292,c_248])).

tff(c_376,plain,(
    '#skF_5'('#skF_2'('#skF_3')) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_373,c_375])).

tff(c_372,plain,(
    v1_finset_1('#skF_5'('#skF_2'('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_291])).

tff(c_84,plain,(
    ! [B_24] :
      ( v1_compts_1('#skF_3')
      | r1_tarski('#skF_5'(B_24),B_24)
      | k6_setfam_1(u1_struct_0('#skF_3'),B_24) != k1_xboole_0
      | ~ v2_tops_2(B_24,'#skF_3')
      | k1_xboole_0 = B_24
      | ~ m1_subset_1(B_24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_520,plain,(
    ! [B_66] :
      ( r1_tarski('#skF_5'(B_66),B_66)
      | k6_setfam_1(u1_struct_0('#skF_3'),B_66) != k1_xboole_0
      | ~ v2_tops_2(B_66,'#skF_3')
      | k1_xboole_0 = B_66
      | ~ m1_subset_1(B_66,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_84])).

tff(c_523,plain,
    ( r1_tarski('#skF_5'('#skF_2'('#skF_3')),'#skF_2'('#skF_3'))
    | k6_setfam_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3')) != k1_xboole_0
    | ~ v2_tops_2('#skF_2'('#skF_3'),'#skF_3')
    | '#skF_2'('#skF_3') = k1_xboole_0
    | v1_compts_1('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_520])).

tff(c_529,plain,
    ( r1_tarski('#skF_5'('#skF_2'('#skF_3')),'#skF_2'('#skF_3'))
    | '#skF_2'('#skF_3') = k1_xboole_0
    | v1_compts_1('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_275,c_292,c_523])).

tff(c_530,plain,(
    r1_tarski('#skF_5'('#skF_2'('#skF_3')),'#skF_2'('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_109,c_373,c_529])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( k1_setfam_1(B_4) != k1_xboole_0
      | ~ v1_finset_1(B_4)
      | ~ r1_tarski(B_4,A_1)
      | k1_xboole_0 = B_4
      | ~ v3_finset_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_543,plain,
    ( k1_setfam_1('#skF_5'('#skF_2'('#skF_3'))) != k1_xboole_0
    | ~ v1_finset_1('#skF_5'('#skF_2'('#skF_3')))
    | '#skF_5'('#skF_2'('#skF_3')) = k1_xboole_0
    | ~ v3_finset_1('#skF_2'('#skF_3')) ),
    inference(resolution,[status(thm)],[c_530,c_2])).

tff(c_558,plain,
    ( k1_setfam_1('#skF_5'('#skF_2'('#skF_3'))) != k1_xboole_0
    | '#skF_5'('#skF_2'('#skF_3')) = k1_xboole_0
    | ~ v3_finset_1('#skF_2'('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_372,c_543])).

tff(c_559,plain,
    ( k1_setfam_1('#skF_5'('#skF_2'('#skF_3'))) != k1_xboole_0
    | ~ v3_finset_1('#skF_2'('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_376,c_558])).

tff(c_561,plain,(
    ~ v3_finset_1('#skF_2'('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_559])).

tff(c_564,plain,
    ( v1_compts_1('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_561])).

tff(c_570,plain,
    ( v1_compts_1('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_564])).

tff(c_572,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_109,c_570])).

tff(c_573,plain,(
    k1_setfam_1('#skF_5'('#skF_2'('#skF_3'))) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_559])).

tff(c_172,plain,(
    ! [A_48] :
      ( m1_subset_1('#skF_2'(A_48),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_48))))
      | v1_compts_1(A_48)
      | ~ l1_pre_topc(A_48)
      | ~ v2_pre_topc(A_48)
      | v2_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_196,plain,(
    ! [A_50] :
      ( r1_tarski('#skF_2'(A_50),k1_zfmisc_1(u1_struct_0(A_50)))
      | v1_compts_1(A_50)
      | ~ l1_pre_topc(A_50)
      | ~ v2_pre_topc(A_50)
      | v2_struct_0(A_50) ) ),
    inference(resolution,[status(thm)],[c_172,c_28])).

tff(c_26,plain,(
    ! [A_11,C_13,B_12] :
      ( r1_tarski(A_11,C_13)
      | ~ r1_tarski(B_12,C_13)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_377,plain,(
    ! [A_55,A_56] :
      ( r1_tarski(A_55,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ r1_tarski(A_55,'#skF_2'(A_56))
      | v1_compts_1(A_56)
      | ~ l1_pre_topc(A_56)
      | ~ v2_pre_topc(A_56)
      | v2_struct_0(A_56) ) ),
    inference(resolution,[status(thm)],[c_196,c_26])).

tff(c_30,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_138,plain,(
    ! [A_37,B_38] :
      ( k6_setfam_1(A_37,B_38) = k1_setfam_1(B_38)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(k1_zfmisc_1(A_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_143,plain,(
    ! [A_37,A_14] :
      ( k6_setfam_1(A_37,A_14) = k1_setfam_1(A_14)
      | ~ r1_tarski(A_14,k1_zfmisc_1(A_37)) ) ),
    inference(resolution,[status(thm)],[c_30,c_138])).

tff(c_387,plain,(
    ! [A_56,A_55] :
      ( k6_setfam_1(u1_struct_0(A_56),A_55) = k1_setfam_1(A_55)
      | ~ r1_tarski(A_55,'#skF_2'(A_56))
      | v1_compts_1(A_56)
      | ~ l1_pre_topc(A_56)
      | ~ v2_pre_topc(A_56)
      | v2_struct_0(A_56) ) ),
    inference(resolution,[status(thm)],[c_377,c_143])).

tff(c_534,plain,
    ( k6_setfam_1(u1_struct_0('#skF_3'),'#skF_5'('#skF_2'('#skF_3'))) = k1_setfam_1('#skF_5'('#skF_2'('#skF_3')))
    | v1_compts_1('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_530,c_387])).

tff(c_548,plain,
    ( k6_setfam_1(u1_struct_0('#skF_3'),'#skF_5'('#skF_2'('#skF_3'))) = k1_setfam_1('#skF_5'('#skF_2'('#skF_3')))
    | v1_compts_1('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_534])).

tff(c_549,plain,(
    k6_setfam_1(u1_struct_0('#skF_3'),'#skF_5'('#skF_2'('#skF_3'))) = k1_setfam_1('#skF_5'('#skF_2'('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_109,c_548])).

tff(c_60,plain,(
    ! [B_24] :
      ( v1_compts_1('#skF_3')
      | k6_setfam_1(u1_struct_0('#skF_3'),'#skF_5'(B_24)) = k1_xboole_0
      | k6_setfam_1(u1_struct_0('#skF_3'),B_24) != k1_xboole_0
      | ~ v2_tops_2(B_24,'#skF_3')
      | k1_xboole_0 = B_24
      | ~ m1_subset_1(B_24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_596,plain,(
    ! [B_68] :
      ( k6_setfam_1(u1_struct_0('#skF_3'),'#skF_5'(B_68)) = k1_xboole_0
      | k6_setfam_1(u1_struct_0('#skF_3'),B_68) != k1_xboole_0
      | ~ v2_tops_2(B_68,'#skF_3')
      | k1_xboole_0 = B_68
      | ~ m1_subset_1(B_68,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_60])).

tff(c_600,plain,
    ( k6_setfam_1(u1_struct_0('#skF_3'),'#skF_5'('#skF_2'('#skF_3'))) = k1_xboole_0
    | k6_setfam_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3')) != k1_xboole_0
    | ~ v2_tops_2('#skF_2'('#skF_3'),'#skF_3')
    | '#skF_2'('#skF_3') = k1_xboole_0
    | v1_compts_1('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_596])).

tff(c_607,plain,
    ( k1_setfam_1('#skF_5'('#skF_2'('#skF_3'))) = k1_xboole_0
    | '#skF_2'('#skF_3') = k1_xboole_0
    | v1_compts_1('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_275,c_292,c_549,c_600])).

tff(c_609,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_109,c_373,c_573,c_607])).

tff(c_610,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_611,plain,(
    v1_compts_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_6,plain,(
    ! [A_1] :
      ( k1_setfam_1('#skF_1'(A_1)) = k1_xboole_0
      | v3_finset_1(A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_8,plain,(
    ! [A_1] :
      ( v1_finset_1('#skF_1'(A_1))
      | v3_finset_1(A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_10,plain,(
    ! [A_1] :
      ( r1_tarski('#skF_1'(A_1),A_1)
      | v3_finset_1(A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_46,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
    | ~ v1_compts_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_644,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_611,c_46])).

tff(c_648,plain,(
    r1_tarski('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_644,c_28])).

tff(c_650,plain,(
    ! [A_77,C_78,B_79] :
      ( r1_tarski(A_77,C_78)
      | ~ r1_tarski(B_79,C_78)
      | ~ r1_tarski(A_77,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_656,plain,(
    ! [A_77] :
      ( r1_tarski(A_77,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(A_77,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_648,c_650])).

tff(c_661,plain,(
    ! [A_81,B_82] :
      ( k6_setfam_1(A_81,B_82) = k1_setfam_1(B_82)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(k1_zfmisc_1(A_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_677,plain,(
    ! [A_84,A_85] :
      ( k6_setfam_1(A_84,A_85) = k1_setfam_1(A_85)
      | ~ r1_tarski(A_85,k1_zfmisc_1(A_84)) ) ),
    inference(resolution,[status(thm)],[c_30,c_661])).

tff(c_688,plain,(
    ! [A_77] :
      ( k6_setfam_1(u1_struct_0('#skF_3'),A_77) = k1_setfam_1(A_77)
      | ~ r1_tarski(A_77,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_656,c_677])).

tff(c_38,plain,(
    ! [C_23] :
      ( k6_setfam_1(u1_struct_0('#skF_3'),C_23) != k1_xboole_0
      | ~ v1_finset_1(C_23)
      | ~ r1_tarski(C_23,'#skF_4')
      | k1_xboole_0 = C_23
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
      | ~ v1_compts_1('#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_711,plain,(
    ! [C_87] :
      ( k6_setfam_1(u1_struct_0('#skF_3'),C_87) != k1_xboole_0
      | ~ v1_finset_1(C_87)
      | ~ r1_tarski(C_87,'#skF_4')
      | k1_xboole_0 = C_87
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_611,c_38])).

tff(c_948,plain,(
    ! [A_105] :
      ( k6_setfam_1(u1_struct_0('#skF_3'),A_105) != k1_xboole_0
      | ~ v1_finset_1(A_105)
      | ~ r1_tarski(A_105,'#skF_4')
      | k1_xboole_0 = A_105
      | ~ r1_tarski(A_105,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_30,c_711])).

tff(c_986,plain,(
    ! [A_106] :
      ( k6_setfam_1(u1_struct_0('#skF_3'),A_106) != k1_xboole_0
      | ~ v1_finset_1(A_106)
      | k1_xboole_0 = A_106
      | ~ r1_tarski(A_106,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_656,c_948])).

tff(c_1018,plain,(
    ! [A_107] :
      ( k1_setfam_1(A_107) != k1_xboole_0
      | ~ v1_finset_1(A_107)
      | k1_xboole_0 = A_107
      | ~ r1_tarski(A_107,'#skF_4')
      | ~ r1_tarski(A_107,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_688,c_986])).

tff(c_1024,plain,
    ( k1_setfam_1('#skF_1'('#skF_4')) != k1_xboole_0
    | ~ v1_finset_1('#skF_1'('#skF_4'))
    | '#skF_1'('#skF_4') = k1_xboole_0
    | ~ r1_tarski('#skF_1'('#skF_4'),'#skF_4')
    | v3_finset_1('#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_10,c_1018])).

tff(c_1030,plain,
    ( k1_setfam_1('#skF_1'('#skF_4')) != k1_xboole_0
    | ~ v1_finset_1('#skF_1'('#skF_4'))
    | '#skF_1'('#skF_4') = k1_xboole_0
    | ~ r1_tarski('#skF_1'('#skF_4'),'#skF_4')
    | v3_finset_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_610,c_1024])).

tff(c_1031,plain,(
    ~ r1_tarski('#skF_1'('#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1030])).

tff(c_1035,plain,
    ( v3_finset_1('#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_10,c_1031])).

tff(c_1038,plain,(
    v3_finset_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_610,c_1035])).

tff(c_42,plain,
    ( v2_tops_2('#skF_4','#skF_3')
    | ~ v1_compts_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_613,plain,(
    v2_tops_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_611,c_42])).

tff(c_40,plain,
    ( k6_setfam_1(u1_struct_0('#skF_3'),'#skF_4') = k1_xboole_0
    | ~ v1_compts_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_615,plain,(
    k6_setfam_1(u1_struct_0('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_611,c_40])).

tff(c_1233,plain,(
    ! [A_135,B_136] :
      ( k6_setfam_1(u1_struct_0(A_135),B_136) != k1_xboole_0
      | ~ v2_tops_2(B_136,A_135)
      | ~ v3_finset_1(B_136)
      | ~ m1_subset_1(B_136,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_135))))
      | ~ v1_compts_1(A_135)
      | ~ l1_pre_topc(A_135)
      | ~ v2_pre_topc(A_135)
      | v2_struct_0(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1239,plain,
    ( k6_setfam_1(u1_struct_0('#skF_3'),'#skF_4') != k1_xboole_0
    | ~ v2_tops_2('#skF_4','#skF_3')
    | ~ v3_finset_1('#skF_4')
    | ~ v1_compts_1('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_644,c_1233])).

tff(c_1247,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_611,c_1038,c_613,c_615,c_1239])).

tff(c_1249,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_1247])).

tff(c_1251,plain,(
    r1_tarski('#skF_1'('#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_1030])).

tff(c_1004,plain,(
    ! [A_77] :
      ( k1_setfam_1(A_77) != k1_xboole_0
      | ~ v1_finset_1(A_77)
      | k1_xboole_0 = A_77
      | ~ r1_tarski(A_77,'#skF_4')
      | ~ r1_tarski(A_77,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_688,c_986])).

tff(c_1253,plain,
    ( k1_setfam_1('#skF_1'('#skF_4')) != k1_xboole_0
    | ~ v1_finset_1('#skF_1'('#skF_4'))
    | '#skF_1'('#skF_4') = k1_xboole_0
    | ~ r1_tarski('#skF_1'('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_1251,c_1004])).

tff(c_1263,plain,
    ( k1_setfam_1('#skF_1'('#skF_4')) != k1_xboole_0
    | ~ v1_finset_1('#skF_1'('#skF_4'))
    | '#skF_1'('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1251,c_1253])).

tff(c_1279,plain,(
    ~ v1_finset_1('#skF_1'('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1263])).

tff(c_1282,plain,
    ( v3_finset_1('#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_8,c_1279])).

tff(c_1285,plain,(
    v3_finset_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_610,c_1282])).

tff(c_1511,plain,(
    ! [A_154,B_155] :
      ( k6_setfam_1(u1_struct_0(A_154),B_155) != k1_xboole_0
      | ~ v2_tops_2(B_155,A_154)
      | ~ v3_finset_1(B_155)
      | ~ m1_subset_1(B_155,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_154))))
      | ~ v1_compts_1(A_154)
      | ~ l1_pre_topc(A_154)
      | ~ v2_pre_topc(A_154)
      | v2_struct_0(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1517,plain,
    ( k6_setfam_1(u1_struct_0('#skF_3'),'#skF_4') != k1_xboole_0
    | ~ v2_tops_2('#skF_4','#skF_3')
    | ~ v3_finset_1('#skF_4')
    | ~ v1_compts_1('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_644,c_1511])).

tff(c_1525,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_611,c_1285,c_613,c_615,c_1517])).

tff(c_1527,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_1525])).

tff(c_1528,plain,
    ( k1_setfam_1('#skF_1'('#skF_4')) != k1_xboole_0
    | '#skF_1'('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1263])).

tff(c_1530,plain,(
    k1_setfam_1('#skF_1'('#skF_4')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1528])).

tff(c_1533,plain,
    ( v3_finset_1('#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1530])).

tff(c_1536,plain,(
    v3_finset_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_610,c_1533])).

tff(c_1816,plain,(
    ! [A_178,B_179] :
      ( k6_setfam_1(u1_struct_0(A_178),B_179) != k1_xboole_0
      | ~ v2_tops_2(B_179,A_178)
      | ~ v3_finset_1(B_179)
      | ~ m1_subset_1(B_179,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_178))))
      | ~ v1_compts_1(A_178)
      | ~ l1_pre_topc(A_178)
      | ~ v2_pre_topc(A_178)
      | v2_struct_0(A_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1822,plain,
    ( k6_setfam_1(u1_struct_0('#skF_3'),'#skF_4') != k1_xboole_0
    | ~ v2_tops_2('#skF_4','#skF_3')
    | ~ v3_finset_1('#skF_4')
    | ~ v1_compts_1('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_644,c_1816])).

tff(c_1830,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_611,c_1536,c_613,c_615,c_1822])).

tff(c_1832,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_1830])).

tff(c_1833,plain,(
    '#skF_1'('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1528])).

tff(c_12,plain,(
    ! [A_1] :
      ( '#skF_1'(A_1) != k1_xboole_0
      | v3_finset_1(A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2118,plain,(
    ! [A_202,B_203] :
      ( k6_setfam_1(u1_struct_0(A_202),B_203) != k1_xboole_0
      | ~ v2_tops_2(B_203,A_202)
      | ~ v3_finset_1(B_203)
      | ~ m1_subset_1(B_203,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_202))))
      | ~ v1_compts_1(A_202)
      | ~ l1_pre_topc(A_202)
      | ~ v2_pre_topc(A_202)
      | v2_struct_0(A_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2124,plain,
    ( k6_setfam_1(u1_struct_0('#skF_3'),'#skF_4') != k1_xboole_0
    | ~ v2_tops_2('#skF_4','#skF_3')
    | ~ v3_finset_1('#skF_4')
    | ~ v1_compts_1('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_644,c_2118])).

tff(c_2132,plain,
    ( ~ v3_finset_1('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_611,c_613,c_615,c_2124])).

tff(c_2133,plain,(
    ~ v3_finset_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_2132])).

tff(c_2137,plain,
    ( '#skF_1'('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_12,c_2133])).

tff(c_2140,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1833,c_2137])).

tff(c_2142,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_610,c_2140])).

%------------------------------------------------------------------------------
