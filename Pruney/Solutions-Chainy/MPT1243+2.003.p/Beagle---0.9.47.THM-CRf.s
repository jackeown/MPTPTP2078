%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:49 EST 2020

% Result     : Theorem 8.41s
% Output     : CNFRefutation 8.41s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 325 expanded)
%              Number of leaves         :   26 ( 113 expanded)
%              Depth                    :   16
%              Number of atoms          :  299 (1149 expanded)
%              Number of equality atoms :   14 (  34 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_104,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> ! [C] :
                  ( r2_hidden(C,B)
                <=> ? [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                      & v3_pre_topc(D,A)
                      & r1_tarski(D,B)
                      & r2_hidden(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_tops_1)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_82,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(c_46,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | r2_hidden('#skF_6','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_186,plain,(
    ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_30,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_28,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_295,plain,(
    ! [A_104,B_105] :
      ( r1_tarski(k1_tops_1(A_104,B_105),B_105)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_pre_topc(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_302,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_295])).

tff(c_309,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_302])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_312,plain,
    ( k1_tops_1('#skF_2','#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_309,c_8])).

tff(c_313,plain,(
    ~ r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_312])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_76,plain,(
    ! [C_69] :
      ( v3_pre_topc('#skF_3','#skF_2')
      | r1_tarski('#skF_7'(C_69),'#skF_3')
      | ~ r2_hidden(C_69,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_204,plain,(
    ! [C_69] :
      ( r1_tarski('#skF_7'(C_69),'#skF_3')
      | ~ r2_hidden(C_69,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_186,c_76])).

tff(c_195,plain,(
    ! [C_84,B_85,A_86] :
      ( r2_hidden(C_84,B_85)
      | ~ r2_hidden(C_84,A_86)
      | ~ r1_tarski(A_86,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_222,plain,(
    ! [A_93,B_94,B_95] :
      ( r2_hidden('#skF_1'(A_93,B_94),B_95)
      | ~ r1_tarski(A_93,B_95)
      | r1_tarski(A_93,B_94) ) ),
    inference(resolution,[status(thm)],[c_6,c_195])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_323,plain,(
    ! [A_110,B_111,B_112,B_113] :
      ( r2_hidden('#skF_1'(A_110,B_111),B_112)
      | ~ r1_tarski(B_113,B_112)
      | ~ r1_tarski(A_110,B_113)
      | r1_tarski(A_110,B_111) ) ),
    inference(resolution,[status(thm)],[c_222,c_2])).

tff(c_411,plain,(
    ! [A_124,B_125,C_126] :
      ( r2_hidden('#skF_1'(A_124,B_125),'#skF_3')
      | ~ r1_tarski(A_124,'#skF_7'(C_126))
      | r1_tarski(A_124,B_125)
      | ~ r2_hidden(C_126,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_204,c_323])).

tff(c_423,plain,(
    ! [C_127,B_128] :
      ( r2_hidden('#skF_1'('#skF_7'(C_127),B_128),'#skF_3')
      | r1_tarski('#skF_7'(C_127),B_128)
      | ~ r2_hidden(C_127,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_12,c_411])).

tff(c_576,plain,(
    ! [C_151,B_152,B_153] :
      ( r2_hidden('#skF_1'('#skF_7'(C_151),B_152),B_153)
      | ~ r1_tarski('#skF_3',B_153)
      | r1_tarski('#skF_7'(C_151),B_152)
      | ~ r2_hidden(C_151,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_423,c_2])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_591,plain,(
    ! [B_153,C_151] :
      ( ~ r1_tarski('#skF_3',B_153)
      | r1_tarski('#skF_7'(C_151),B_153)
      | ~ r2_hidden(C_151,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_576,c_4])).

tff(c_120,plain,(
    ! [C_69] :
      ( v3_pre_topc('#skF_3','#skF_2')
      | m1_subset_1('#skF_7'(C_69),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(C_69,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_231,plain,(
    ! [C_69] :
      ( m1_subset_1('#skF_7'(C_69),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(C_69,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_186,c_120])).

tff(c_98,plain,(
    ! [C_69] :
      ( v3_pre_topc('#skF_3','#skF_2')
      | v3_pre_topc('#skF_7'(C_69),'#skF_2')
      | ~ r2_hidden(C_69,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_209,plain,(
    ! [C_69] :
      ( v3_pre_topc('#skF_7'(C_69),'#skF_2')
      | ~ r2_hidden(C_69,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_186,c_98])).

tff(c_24,plain,(
    ! [B_28,D_34,C_32,A_20] :
      ( k1_tops_1(B_28,D_34) = D_34
      | ~ v3_pre_topc(D_34,B_28)
      | ~ m1_subset_1(D_34,k1_zfmisc_1(u1_struct_0(B_28)))
      | ~ m1_subset_1(C_32,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_pre_topc(B_28)
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1060,plain,(
    ! [C_202,A_203] :
      ( ~ m1_subset_1(C_202,k1_zfmisc_1(u1_struct_0(A_203)))
      | ~ l1_pre_topc(A_203)
      | ~ v2_pre_topc(A_203) ) ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_1070,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_1060])).

tff(c_1078,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_1070])).

tff(c_1080,plain,(
    ! [B_204,D_205] :
      ( k1_tops_1(B_204,D_205) = D_205
      | ~ v3_pre_topc(D_205,B_204)
      | ~ m1_subset_1(D_205,k1_zfmisc_1(u1_struct_0(B_204)))
      | ~ l1_pre_topc(B_204) ) ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_1083,plain,(
    ! [C_69] :
      ( k1_tops_1('#skF_2','#skF_7'(C_69)) = '#skF_7'(C_69)
      | ~ v3_pre_topc('#skF_7'(C_69),'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ r2_hidden(C_69,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_231,c_1080])).

tff(c_1198,plain,(
    ! [C_210] :
      ( k1_tops_1('#skF_2','#skF_7'(C_210)) = '#skF_7'(C_210)
      | ~ v3_pre_topc('#skF_7'(C_210),'#skF_2')
      | ~ r2_hidden(C_210,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1083])).

tff(c_1207,plain,(
    ! [C_211] :
      ( k1_tops_1('#skF_2','#skF_7'(C_211)) = '#skF_7'(C_211)
      | ~ r2_hidden(C_211,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_209,c_1198])).

tff(c_20,plain,(
    ! [A_13,B_17,C_19] :
      ( r1_tarski(k1_tops_1(A_13,B_17),k1_tops_1(A_13,C_19))
      | ~ r1_tarski(B_17,C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1224,plain,(
    ! [C_211,C_19] :
      ( r1_tarski('#skF_7'(C_211),k1_tops_1('#skF_2',C_19))
      | ~ r1_tarski('#skF_7'(C_211),C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_7'(C_211),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ r2_hidden(C_211,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1207,c_20])).

tff(c_4506,plain,(
    ! [C_447,C_448] :
      ( r1_tarski('#skF_7'(C_447),k1_tops_1('#skF_2',C_448))
      | ~ r1_tarski('#skF_7'(C_447),C_448)
      | ~ m1_subset_1(C_448,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_7'(C_447),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(C_447,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1224])).

tff(c_4514,plain,(
    ! [C_449,C_450] :
      ( r1_tarski('#skF_7'(C_449),k1_tops_1('#skF_2',C_450))
      | ~ r1_tarski('#skF_7'(C_449),C_450)
      | ~ m1_subset_1(C_450,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(C_449,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_231,c_4506])).

tff(c_54,plain,(
    ! [C_69] :
      ( v3_pre_topc('#skF_3','#skF_2')
      | r2_hidden(C_69,'#skF_7'(C_69))
      | ~ r2_hidden(C_69,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_200,plain,(
    ! [C_87] :
      ( r2_hidden(C_87,'#skF_7'(C_87))
      | ~ r2_hidden(C_87,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_186,c_54])).

tff(c_203,plain,(
    ! [C_87,B_2] :
      ( r2_hidden(C_87,B_2)
      | ~ r1_tarski('#skF_7'(C_87),B_2)
      | ~ r2_hidden(C_87,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_200,c_2])).

tff(c_4658,plain,(
    ! [C_451,C_452] :
      ( r2_hidden(C_451,k1_tops_1('#skF_2',C_452))
      | ~ r1_tarski('#skF_7'(C_451),C_452)
      | ~ m1_subset_1(C_452,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(C_451,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_4514,c_203])).

tff(c_4669,plain,(
    ! [C_453] :
      ( r2_hidden(C_453,k1_tops_1('#skF_2','#skF_3'))
      | ~ r1_tarski('#skF_7'(C_453),'#skF_3')
      | ~ r2_hidden(C_453,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26,c_4658])).

tff(c_5125,plain,(
    ! [A_474] :
      ( r1_tarski(A_474,k1_tops_1('#skF_2','#skF_3'))
      | ~ r1_tarski('#skF_7'('#skF_1'(A_474,k1_tops_1('#skF_2','#skF_3'))),'#skF_3')
      | ~ r2_hidden('#skF_1'(A_474,k1_tops_1('#skF_2','#skF_3')),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_4669,c_4])).

tff(c_5128,plain,(
    ! [A_474] :
      ( r1_tarski(A_474,k1_tops_1('#skF_2','#skF_3'))
      | ~ r1_tarski('#skF_3','#skF_3')
      | ~ r2_hidden('#skF_1'(A_474,k1_tops_1('#skF_2','#skF_3')),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_591,c_5125])).

tff(c_5136,plain,(
    ! [A_475] :
      ( r1_tarski(A_475,k1_tops_1('#skF_2','#skF_3'))
      | ~ r2_hidden('#skF_1'(A_475,k1_tops_1('#skF_2','#skF_3')),'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_5128])).

tff(c_5212,plain,(
    r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_5136])).

tff(c_5243,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_313,c_313,c_5212])).

tff(c_5244,plain,(
    k1_tops_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_312])).

tff(c_22,plain,(
    ! [C_32,A_20,D_34,B_28] :
      ( v3_pre_topc(C_32,A_20)
      | k1_tops_1(A_20,C_32) != C_32
      | ~ m1_subset_1(D_34,k1_zfmisc_1(u1_struct_0(B_28)))
      | ~ m1_subset_1(C_32,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_pre_topc(B_28)
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_5780,plain,(
    ! [D_548,B_549] :
      ( ~ m1_subset_1(D_548,k1_zfmisc_1(u1_struct_0(B_549)))
      | ~ l1_pre_topc(B_549) ) ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_5790,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_5780])).

tff(c_5798,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_5790])).

tff(c_5878,plain,(
    ! [C_556,A_557] :
      ( v3_pre_topc(C_556,A_557)
      | k1_tops_1(A_557,C_556) != C_556
      | ~ m1_subset_1(C_556,k1_zfmisc_1(u1_struct_0(A_557)))
      | ~ l1_pre_topc(A_557)
      | ~ v2_pre_topc(A_557) ) ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_5888,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | k1_tops_1('#skF_2','#skF_3') != '#skF_3'
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_5878])).

tff(c_5895,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_5244,c_5888])).

tff(c_5897,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_186,c_5895])).

tff(c_5899,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_50,plain,
    ( v3_pre_topc('#skF_5','#skF_2')
    | r2_hidden('#skF_6','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_5902,plain,
    ( v3_pre_topc('#skF_5','#skF_2')
    | r2_hidden('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5899,c_50])).

tff(c_5903,plain,(
    r2_hidden('#skF_6','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_5902])).

tff(c_165,plain,(
    ! [A_74,B_75] :
      ( r1_tarski(A_74,B_75)
      | ~ m1_subset_1(A_74,k1_zfmisc_1(B_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_169,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_26,c_165])).

tff(c_5898,plain,
    ( r2_hidden('#skF_6','#skF_3')
    | r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_5900,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_5898])).

tff(c_5916,plain,(
    ! [C_562,B_563,A_564] :
      ( r2_hidden(C_562,B_563)
      | ~ r2_hidden(C_562,A_564)
      | ~ r1_tarski(A_564,B_563) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5930,plain,(
    ! [B_566] :
      ( r2_hidden('#skF_4',B_566)
      | ~ r1_tarski('#skF_5',B_566) ) ),
    inference(resolution,[status(thm)],[c_5900,c_5916])).

tff(c_5954,plain,(
    ! [B_570,B_571] :
      ( r2_hidden('#skF_4',B_570)
      | ~ r1_tarski(B_571,B_570)
      | ~ r1_tarski('#skF_5',B_571) ) ),
    inference(resolution,[status(thm)],[c_5930,c_2])).

tff(c_5959,plain,
    ( r2_hidden('#skF_4',u1_struct_0('#skF_2'))
    | ~ r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_169,c_5954])).

tff(c_5961,plain,(
    ~ r1_tarski('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_5959])).

tff(c_38,plain,(
    ! [D_68] :
      ( r1_tarski('#skF_5','#skF_3')
      | ~ r2_hidden('#skF_6',D_68)
      | ~ r1_tarski(D_68,'#skF_3')
      | ~ v3_pre_topc(D_68,'#skF_2')
      | ~ m1_subset_1(D_68,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc('#skF_3','#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_6263,plain,(
    ! [D_68] :
      ( r1_tarski('#skF_5','#skF_3')
      | ~ r2_hidden('#skF_6',D_68)
      | ~ r1_tarski(D_68,'#skF_3')
      | ~ v3_pre_topc(D_68,'#skF_2')
      | ~ m1_subset_1(D_68,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5899,c_38])).

tff(c_6265,plain,(
    ! [D_617] :
      ( ~ r2_hidden('#skF_6',D_617)
      | ~ r1_tarski(D_617,'#skF_3')
      | ~ v3_pre_topc(D_617,'#skF_2')
      | ~ m1_subset_1(D_617,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_5961,c_6263])).

tff(c_6272,plain,
    ( ~ r2_hidden('#skF_6','#skF_3')
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_6265])).

tff(c_6277,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5899,c_12,c_5903,c_6272])).

tff(c_6279,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_5959])).

tff(c_5933,plain,(
    ! [B_2,B_566] :
      ( r2_hidden('#skF_4',B_2)
      | ~ r1_tarski(B_566,B_2)
      | ~ r1_tarski('#skF_5',B_566) ) ),
    inference(resolution,[status(thm)],[c_5930,c_2])).

tff(c_6281,plain,
    ( r2_hidden('#skF_4','#skF_3')
    | ~ r1_tarski('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_6279,c_5933])).

tff(c_6288,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_6281])).

tff(c_34,plain,(
    ! [D_68] :
      ( ~ r2_hidden('#skF_4','#skF_3')
      | ~ r2_hidden('#skF_6',D_68)
      | ~ r1_tarski(D_68,'#skF_3')
      | ~ v3_pre_topc(D_68,'#skF_2')
      | ~ m1_subset_1(D_68,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc('#skF_3','#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_6724,plain,(
    ! [D_669] :
      ( ~ r2_hidden('#skF_6',D_669)
      | ~ r1_tarski(D_669,'#skF_3')
      | ~ v3_pre_topc(D_669,'#skF_2')
      | ~ m1_subset_1(D_669,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5899,c_6288,c_34])).

tff(c_6731,plain,
    ( ~ r2_hidden('#skF_6','#skF_3')
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_6724])).

tff(c_6736,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5899,c_12,c_5903,c_6731])).

tff(c_6738,plain,(
    ~ r2_hidden('#skF_6','#skF_3') ),
    inference(splitRight,[status(thm)],[c_5902])).

tff(c_48,plain,
    ( r1_tarski('#skF_5','#skF_3')
    | r2_hidden('#skF_6','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_6748,plain,
    ( r1_tarski('#skF_5','#skF_3')
    | r2_hidden('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5899,c_48])).

tff(c_6749,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_6738,c_6748])).

tff(c_6754,plain,(
    ! [C_674,B_675,A_676] :
      ( r2_hidden(C_674,B_675)
      | ~ r2_hidden(C_674,A_676)
      | ~ r1_tarski(A_676,B_675) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6764,plain,(
    ! [B_677] :
      ( r2_hidden('#skF_4',B_677)
      | ~ r1_tarski('#skF_5',B_677) ) ),
    inference(resolution,[status(thm)],[c_5900,c_6754])).

tff(c_44,plain,
    ( ~ r2_hidden('#skF_4','#skF_3')
    | r2_hidden('#skF_6','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_6762,plain,
    ( ~ r2_hidden('#skF_4','#skF_3')
    | r2_hidden('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5899,c_44])).

tff(c_6763,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_6738,c_6762])).

tff(c_6767,plain,(
    ~ r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_6764,c_6763])).

tff(c_6773,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6749,c_6767])).

tff(c_6774,plain,(
    r2_hidden('#skF_6','#skF_3') ),
    inference(splitRight,[status(thm)],[c_5898])).

tff(c_6775,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_5898])).

tff(c_36,plain,(
    ! [D_68] :
      ( r2_hidden('#skF_4','#skF_5')
      | ~ r2_hidden('#skF_6',D_68)
      | ~ r1_tarski(D_68,'#skF_3')
      | ~ v3_pre_topc(D_68,'#skF_2')
      | ~ m1_subset_1(D_68,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc('#skF_3','#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_7066,plain,(
    ! [D_68] :
      ( r2_hidden('#skF_4','#skF_5')
      | ~ r2_hidden('#skF_6',D_68)
      | ~ r1_tarski(D_68,'#skF_3')
      | ~ v3_pre_topc(D_68,'#skF_2')
      | ~ m1_subset_1(D_68,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5899,c_36])).

tff(c_7068,plain,(
    ! [D_722] :
      ( ~ r2_hidden('#skF_6',D_722)
      | ~ r1_tarski(D_722,'#skF_3')
      | ~ v3_pre_topc(D_722,'#skF_2')
      | ~ m1_subset_1(D_722,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_6775,c_7066])).

tff(c_7075,plain,
    ( ~ r2_hidden('#skF_6','#skF_3')
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_7068])).

tff(c_7080,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5899,c_12,c_6774,c_7075])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:28:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.41/2.97  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.41/2.98  
% 8.41/2.98  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.41/2.98  %$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 8.41/2.98  
% 8.41/2.98  %Foreground sorts:
% 8.41/2.98  
% 8.41/2.98  
% 8.41/2.98  %Background operators:
% 8.41/2.98  
% 8.41/2.98  
% 8.41/2.98  %Foreground operators:
% 8.41/2.98  tff('#skF_7', type, '#skF_7': $i > $i).
% 8.41/2.98  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 8.41/2.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.41/2.98  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.41/2.98  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.41/2.98  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.41/2.98  tff('#skF_5', type, '#skF_5': $i).
% 8.41/2.98  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 8.41/2.98  tff('#skF_6', type, '#skF_6': $i).
% 8.41/2.98  tff('#skF_2', type, '#skF_2': $i).
% 8.41/2.98  tff('#skF_3', type, '#skF_3': $i).
% 8.41/2.98  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.41/2.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.41/2.98  tff('#skF_4', type, '#skF_4': $i).
% 8.41/2.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.41/2.98  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.41/2.98  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.41/2.98  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.41/2.98  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.41/2.98  
% 8.41/3.01  tff(f_104, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, B)) & r2_hidden(C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_tops_1)).
% 8.41/3.01  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 8.41/3.01  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.41/3.01  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 8.41/3.01  tff(f_82, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_1)).
% 8.41/3.01  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 8.41/3.01  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 8.41/3.01  tff(c_46, plain, (r2_hidden('#skF_4', '#skF_5') | r2_hidden('#skF_6', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.41/3.01  tff(c_186, plain, (~v3_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_46])).
% 8.41/3.01  tff(c_30, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.41/3.01  tff(c_28, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.41/3.01  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.41/3.01  tff(c_295, plain, (![A_104, B_105]: (r1_tarski(k1_tops_1(A_104, B_105), B_105) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_104))) | ~l1_pre_topc(A_104))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.41/3.01  tff(c_302, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_26, c_295])).
% 8.41/3.01  tff(c_309, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_302])).
% 8.41/3.01  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.41/3.01  tff(c_312, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_309, c_8])).
% 8.41/3.01  tff(c_313, plain, (~r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_312])).
% 8.41/3.01  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.41/3.01  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.41/3.01  tff(c_76, plain, (![C_69]: (v3_pre_topc('#skF_3', '#skF_2') | r1_tarski('#skF_7'(C_69), '#skF_3') | ~r2_hidden(C_69, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.41/3.01  tff(c_204, plain, (![C_69]: (r1_tarski('#skF_7'(C_69), '#skF_3') | ~r2_hidden(C_69, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_186, c_76])).
% 8.41/3.01  tff(c_195, plain, (![C_84, B_85, A_86]: (r2_hidden(C_84, B_85) | ~r2_hidden(C_84, A_86) | ~r1_tarski(A_86, B_85))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.41/3.01  tff(c_222, plain, (![A_93, B_94, B_95]: (r2_hidden('#skF_1'(A_93, B_94), B_95) | ~r1_tarski(A_93, B_95) | r1_tarski(A_93, B_94))), inference(resolution, [status(thm)], [c_6, c_195])).
% 8.41/3.01  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.41/3.01  tff(c_323, plain, (![A_110, B_111, B_112, B_113]: (r2_hidden('#skF_1'(A_110, B_111), B_112) | ~r1_tarski(B_113, B_112) | ~r1_tarski(A_110, B_113) | r1_tarski(A_110, B_111))), inference(resolution, [status(thm)], [c_222, c_2])).
% 8.41/3.01  tff(c_411, plain, (![A_124, B_125, C_126]: (r2_hidden('#skF_1'(A_124, B_125), '#skF_3') | ~r1_tarski(A_124, '#skF_7'(C_126)) | r1_tarski(A_124, B_125) | ~r2_hidden(C_126, '#skF_3'))), inference(resolution, [status(thm)], [c_204, c_323])).
% 8.41/3.01  tff(c_423, plain, (![C_127, B_128]: (r2_hidden('#skF_1'('#skF_7'(C_127), B_128), '#skF_3') | r1_tarski('#skF_7'(C_127), B_128) | ~r2_hidden(C_127, '#skF_3'))), inference(resolution, [status(thm)], [c_12, c_411])).
% 8.41/3.01  tff(c_576, plain, (![C_151, B_152, B_153]: (r2_hidden('#skF_1'('#skF_7'(C_151), B_152), B_153) | ~r1_tarski('#skF_3', B_153) | r1_tarski('#skF_7'(C_151), B_152) | ~r2_hidden(C_151, '#skF_3'))), inference(resolution, [status(thm)], [c_423, c_2])).
% 8.41/3.01  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.41/3.01  tff(c_591, plain, (![B_153, C_151]: (~r1_tarski('#skF_3', B_153) | r1_tarski('#skF_7'(C_151), B_153) | ~r2_hidden(C_151, '#skF_3'))), inference(resolution, [status(thm)], [c_576, c_4])).
% 8.41/3.01  tff(c_120, plain, (![C_69]: (v3_pre_topc('#skF_3', '#skF_2') | m1_subset_1('#skF_7'(C_69), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden(C_69, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.41/3.01  tff(c_231, plain, (![C_69]: (m1_subset_1('#skF_7'(C_69), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden(C_69, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_186, c_120])).
% 8.41/3.01  tff(c_98, plain, (![C_69]: (v3_pre_topc('#skF_3', '#skF_2') | v3_pre_topc('#skF_7'(C_69), '#skF_2') | ~r2_hidden(C_69, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.41/3.01  tff(c_209, plain, (![C_69]: (v3_pre_topc('#skF_7'(C_69), '#skF_2') | ~r2_hidden(C_69, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_186, c_98])).
% 8.41/3.01  tff(c_24, plain, (![B_28, D_34, C_32, A_20]: (k1_tops_1(B_28, D_34)=D_34 | ~v3_pre_topc(D_34, B_28) | ~m1_subset_1(D_34, k1_zfmisc_1(u1_struct_0(B_28))) | ~m1_subset_1(C_32, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_pre_topc(B_28) | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.41/3.01  tff(c_1060, plain, (![C_202, A_203]: (~m1_subset_1(C_202, k1_zfmisc_1(u1_struct_0(A_203))) | ~l1_pre_topc(A_203) | ~v2_pre_topc(A_203))), inference(splitLeft, [status(thm)], [c_24])).
% 8.41/3.01  tff(c_1070, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_26, c_1060])).
% 8.41/3.01  tff(c_1078, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_1070])).
% 8.41/3.01  tff(c_1080, plain, (![B_204, D_205]: (k1_tops_1(B_204, D_205)=D_205 | ~v3_pre_topc(D_205, B_204) | ~m1_subset_1(D_205, k1_zfmisc_1(u1_struct_0(B_204))) | ~l1_pre_topc(B_204))), inference(splitRight, [status(thm)], [c_24])).
% 8.41/3.01  tff(c_1083, plain, (![C_69]: (k1_tops_1('#skF_2', '#skF_7'(C_69))='#skF_7'(C_69) | ~v3_pre_topc('#skF_7'(C_69), '#skF_2') | ~l1_pre_topc('#skF_2') | ~r2_hidden(C_69, '#skF_3'))), inference(resolution, [status(thm)], [c_231, c_1080])).
% 8.41/3.01  tff(c_1198, plain, (![C_210]: (k1_tops_1('#skF_2', '#skF_7'(C_210))='#skF_7'(C_210) | ~v3_pre_topc('#skF_7'(C_210), '#skF_2') | ~r2_hidden(C_210, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1083])).
% 8.41/3.01  tff(c_1207, plain, (![C_211]: (k1_tops_1('#skF_2', '#skF_7'(C_211))='#skF_7'(C_211) | ~r2_hidden(C_211, '#skF_3'))), inference(resolution, [status(thm)], [c_209, c_1198])).
% 8.41/3.01  tff(c_20, plain, (![A_13, B_17, C_19]: (r1_tarski(k1_tops_1(A_13, B_17), k1_tops_1(A_13, C_19)) | ~r1_tarski(B_17, C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(u1_struct_0(A_13))) | ~m1_subset_1(B_17, k1_zfmisc_1(u1_struct_0(A_13))) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.41/3.01  tff(c_1224, plain, (![C_211, C_19]: (r1_tarski('#skF_7'(C_211), k1_tops_1('#skF_2', C_19)) | ~r1_tarski('#skF_7'(C_211), C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_7'(C_211), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~r2_hidden(C_211, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1207, c_20])).
% 8.41/3.01  tff(c_4506, plain, (![C_447, C_448]: (r1_tarski('#skF_7'(C_447), k1_tops_1('#skF_2', C_448)) | ~r1_tarski('#skF_7'(C_447), C_448) | ~m1_subset_1(C_448, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_7'(C_447), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden(C_447, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1224])).
% 8.41/3.01  tff(c_4514, plain, (![C_449, C_450]: (r1_tarski('#skF_7'(C_449), k1_tops_1('#skF_2', C_450)) | ~r1_tarski('#skF_7'(C_449), C_450) | ~m1_subset_1(C_450, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden(C_449, '#skF_3'))), inference(resolution, [status(thm)], [c_231, c_4506])).
% 8.41/3.01  tff(c_54, plain, (![C_69]: (v3_pre_topc('#skF_3', '#skF_2') | r2_hidden(C_69, '#skF_7'(C_69)) | ~r2_hidden(C_69, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.41/3.01  tff(c_200, plain, (![C_87]: (r2_hidden(C_87, '#skF_7'(C_87)) | ~r2_hidden(C_87, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_186, c_54])).
% 8.41/3.01  tff(c_203, plain, (![C_87, B_2]: (r2_hidden(C_87, B_2) | ~r1_tarski('#skF_7'(C_87), B_2) | ~r2_hidden(C_87, '#skF_3'))), inference(resolution, [status(thm)], [c_200, c_2])).
% 8.41/3.01  tff(c_4658, plain, (![C_451, C_452]: (r2_hidden(C_451, k1_tops_1('#skF_2', C_452)) | ~r1_tarski('#skF_7'(C_451), C_452) | ~m1_subset_1(C_452, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden(C_451, '#skF_3'))), inference(resolution, [status(thm)], [c_4514, c_203])).
% 8.41/3.01  tff(c_4669, plain, (![C_453]: (r2_hidden(C_453, k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski('#skF_7'(C_453), '#skF_3') | ~r2_hidden(C_453, '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_4658])).
% 8.41/3.01  tff(c_5125, plain, (![A_474]: (r1_tarski(A_474, k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski('#skF_7'('#skF_1'(A_474, k1_tops_1('#skF_2', '#skF_3'))), '#skF_3') | ~r2_hidden('#skF_1'(A_474, k1_tops_1('#skF_2', '#skF_3')), '#skF_3'))), inference(resolution, [status(thm)], [c_4669, c_4])).
% 8.41/3.01  tff(c_5128, plain, (![A_474]: (r1_tarski(A_474, k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski('#skF_3', '#skF_3') | ~r2_hidden('#skF_1'(A_474, k1_tops_1('#skF_2', '#skF_3')), '#skF_3'))), inference(resolution, [status(thm)], [c_591, c_5125])).
% 8.41/3.01  tff(c_5136, plain, (![A_475]: (r1_tarski(A_475, k1_tops_1('#skF_2', '#skF_3')) | ~r2_hidden('#skF_1'(A_475, k1_tops_1('#skF_2', '#skF_3')), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_5128])).
% 8.41/3.01  tff(c_5212, plain, (r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_6, c_5136])).
% 8.41/3.01  tff(c_5243, plain, $false, inference(negUnitSimplification, [status(thm)], [c_313, c_313, c_5212])).
% 8.41/3.01  tff(c_5244, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_312])).
% 8.41/3.01  tff(c_22, plain, (![C_32, A_20, D_34, B_28]: (v3_pre_topc(C_32, A_20) | k1_tops_1(A_20, C_32)!=C_32 | ~m1_subset_1(D_34, k1_zfmisc_1(u1_struct_0(B_28))) | ~m1_subset_1(C_32, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_pre_topc(B_28) | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.41/3.01  tff(c_5780, plain, (![D_548, B_549]: (~m1_subset_1(D_548, k1_zfmisc_1(u1_struct_0(B_549))) | ~l1_pre_topc(B_549))), inference(splitLeft, [status(thm)], [c_22])).
% 8.41/3.01  tff(c_5790, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_26, c_5780])).
% 8.41/3.01  tff(c_5798, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_5790])).
% 8.41/3.01  tff(c_5878, plain, (![C_556, A_557]: (v3_pre_topc(C_556, A_557) | k1_tops_1(A_557, C_556)!=C_556 | ~m1_subset_1(C_556, k1_zfmisc_1(u1_struct_0(A_557))) | ~l1_pre_topc(A_557) | ~v2_pre_topc(A_557))), inference(splitRight, [status(thm)], [c_22])).
% 8.41/3.01  tff(c_5888, plain, (v3_pre_topc('#skF_3', '#skF_2') | k1_tops_1('#skF_2', '#skF_3')!='#skF_3' | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_26, c_5878])).
% 8.41/3.01  tff(c_5895, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_5244, c_5888])).
% 8.41/3.01  tff(c_5897, plain, $false, inference(negUnitSimplification, [status(thm)], [c_186, c_5895])).
% 8.41/3.01  tff(c_5899, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_46])).
% 8.41/3.01  tff(c_50, plain, (v3_pre_topc('#skF_5', '#skF_2') | r2_hidden('#skF_6', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.41/3.01  tff(c_5902, plain, (v3_pre_topc('#skF_5', '#skF_2') | r2_hidden('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5899, c_50])).
% 8.41/3.01  tff(c_5903, plain, (r2_hidden('#skF_6', '#skF_3')), inference(splitLeft, [status(thm)], [c_5902])).
% 8.41/3.01  tff(c_165, plain, (![A_74, B_75]: (r1_tarski(A_74, B_75) | ~m1_subset_1(A_74, k1_zfmisc_1(B_75)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.41/3.01  tff(c_169, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_26, c_165])).
% 8.41/3.01  tff(c_5898, plain, (r2_hidden('#skF_6', '#skF_3') | r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_46])).
% 8.41/3.01  tff(c_5900, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_5898])).
% 8.41/3.01  tff(c_5916, plain, (![C_562, B_563, A_564]: (r2_hidden(C_562, B_563) | ~r2_hidden(C_562, A_564) | ~r1_tarski(A_564, B_563))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.41/3.01  tff(c_5930, plain, (![B_566]: (r2_hidden('#skF_4', B_566) | ~r1_tarski('#skF_5', B_566))), inference(resolution, [status(thm)], [c_5900, c_5916])).
% 8.41/3.01  tff(c_5954, plain, (![B_570, B_571]: (r2_hidden('#skF_4', B_570) | ~r1_tarski(B_571, B_570) | ~r1_tarski('#skF_5', B_571))), inference(resolution, [status(thm)], [c_5930, c_2])).
% 8.41/3.01  tff(c_5959, plain, (r2_hidden('#skF_4', u1_struct_0('#skF_2')) | ~r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_169, c_5954])).
% 8.41/3.01  tff(c_5961, plain, (~r1_tarski('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_5959])).
% 8.41/3.01  tff(c_38, plain, (![D_68]: (r1_tarski('#skF_5', '#skF_3') | ~r2_hidden('#skF_6', D_68) | ~r1_tarski(D_68, '#skF_3') | ~v3_pre_topc(D_68, '#skF_2') | ~m1_subset_1(D_68, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.41/3.01  tff(c_6263, plain, (![D_68]: (r1_tarski('#skF_5', '#skF_3') | ~r2_hidden('#skF_6', D_68) | ~r1_tarski(D_68, '#skF_3') | ~v3_pre_topc(D_68, '#skF_2') | ~m1_subset_1(D_68, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_5899, c_38])).
% 8.41/3.01  tff(c_6265, plain, (![D_617]: (~r2_hidden('#skF_6', D_617) | ~r1_tarski(D_617, '#skF_3') | ~v3_pre_topc(D_617, '#skF_2') | ~m1_subset_1(D_617, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_5961, c_6263])).
% 8.41/3.01  tff(c_6272, plain, (~r2_hidden('#skF_6', '#skF_3') | ~r1_tarski('#skF_3', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_26, c_6265])).
% 8.41/3.01  tff(c_6277, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5899, c_12, c_5903, c_6272])).
% 8.41/3.01  tff(c_6279, plain, (r1_tarski('#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_5959])).
% 8.41/3.01  tff(c_5933, plain, (![B_2, B_566]: (r2_hidden('#skF_4', B_2) | ~r1_tarski(B_566, B_2) | ~r1_tarski('#skF_5', B_566))), inference(resolution, [status(thm)], [c_5930, c_2])).
% 8.41/3.01  tff(c_6281, plain, (r2_hidden('#skF_4', '#skF_3') | ~r1_tarski('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_6279, c_5933])).
% 8.41/3.01  tff(c_6288, plain, (r2_hidden('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_6281])).
% 8.41/3.01  tff(c_34, plain, (![D_68]: (~r2_hidden('#skF_4', '#skF_3') | ~r2_hidden('#skF_6', D_68) | ~r1_tarski(D_68, '#skF_3') | ~v3_pre_topc(D_68, '#skF_2') | ~m1_subset_1(D_68, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.41/3.01  tff(c_6724, plain, (![D_669]: (~r2_hidden('#skF_6', D_669) | ~r1_tarski(D_669, '#skF_3') | ~v3_pre_topc(D_669, '#skF_2') | ~m1_subset_1(D_669, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_5899, c_6288, c_34])).
% 8.41/3.01  tff(c_6731, plain, (~r2_hidden('#skF_6', '#skF_3') | ~r1_tarski('#skF_3', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_26, c_6724])).
% 8.41/3.01  tff(c_6736, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5899, c_12, c_5903, c_6731])).
% 8.41/3.01  tff(c_6738, plain, (~r2_hidden('#skF_6', '#skF_3')), inference(splitRight, [status(thm)], [c_5902])).
% 8.41/3.01  tff(c_48, plain, (r1_tarski('#skF_5', '#skF_3') | r2_hidden('#skF_6', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.41/3.01  tff(c_6748, plain, (r1_tarski('#skF_5', '#skF_3') | r2_hidden('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5899, c_48])).
% 8.41/3.01  tff(c_6749, plain, (r1_tarski('#skF_5', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_6738, c_6748])).
% 8.41/3.01  tff(c_6754, plain, (![C_674, B_675, A_676]: (r2_hidden(C_674, B_675) | ~r2_hidden(C_674, A_676) | ~r1_tarski(A_676, B_675))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.41/3.01  tff(c_6764, plain, (![B_677]: (r2_hidden('#skF_4', B_677) | ~r1_tarski('#skF_5', B_677))), inference(resolution, [status(thm)], [c_5900, c_6754])).
% 8.41/3.01  tff(c_44, plain, (~r2_hidden('#skF_4', '#skF_3') | r2_hidden('#skF_6', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.41/3.01  tff(c_6762, plain, (~r2_hidden('#skF_4', '#skF_3') | r2_hidden('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5899, c_44])).
% 8.41/3.01  tff(c_6763, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_6738, c_6762])).
% 8.41/3.01  tff(c_6767, plain, (~r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_6764, c_6763])).
% 8.41/3.01  tff(c_6773, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6749, c_6767])).
% 8.41/3.01  tff(c_6774, plain, (r2_hidden('#skF_6', '#skF_3')), inference(splitRight, [status(thm)], [c_5898])).
% 8.41/3.01  tff(c_6775, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_5898])).
% 8.41/3.01  tff(c_36, plain, (![D_68]: (r2_hidden('#skF_4', '#skF_5') | ~r2_hidden('#skF_6', D_68) | ~r1_tarski(D_68, '#skF_3') | ~v3_pre_topc(D_68, '#skF_2') | ~m1_subset_1(D_68, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.41/3.01  tff(c_7066, plain, (![D_68]: (r2_hidden('#skF_4', '#skF_5') | ~r2_hidden('#skF_6', D_68) | ~r1_tarski(D_68, '#skF_3') | ~v3_pre_topc(D_68, '#skF_2') | ~m1_subset_1(D_68, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_5899, c_36])).
% 8.41/3.01  tff(c_7068, plain, (![D_722]: (~r2_hidden('#skF_6', D_722) | ~r1_tarski(D_722, '#skF_3') | ~v3_pre_topc(D_722, '#skF_2') | ~m1_subset_1(D_722, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_6775, c_7066])).
% 8.41/3.01  tff(c_7075, plain, (~r2_hidden('#skF_6', '#skF_3') | ~r1_tarski('#skF_3', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_26, c_7068])).
% 8.41/3.01  tff(c_7080, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5899, c_12, c_6774, c_7075])).
% 8.41/3.01  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.41/3.01  
% 8.41/3.01  Inference rules
% 8.41/3.01  ----------------------
% 8.41/3.01  #Ref     : 0
% 8.41/3.01  #Sup     : 1618
% 8.41/3.01  #Fact    : 0
% 8.41/3.01  #Define  : 0
% 8.41/3.01  #Split   : 28
% 8.41/3.01  #Chain   : 0
% 8.41/3.01  #Close   : 0
% 8.41/3.01  
% 8.41/3.01  Ordering : KBO
% 8.41/3.01  
% 8.41/3.01  Simplification rules
% 8.41/3.01  ----------------------
% 8.41/3.01  #Subsume      : 739
% 8.41/3.01  #Demod        : 556
% 8.41/3.01  #Tautology    : 214
% 8.41/3.01  #SimpNegUnit  : 29
% 8.41/3.01  #BackRed      : 1
% 8.41/3.01  
% 8.41/3.01  #Partial instantiations: 0
% 8.41/3.01  #Strategies tried      : 1
% 8.41/3.01  
% 8.41/3.01  Timing (in seconds)
% 8.41/3.01  ----------------------
% 8.41/3.01  Preprocessing        : 0.34
% 8.41/3.01  Parsing              : 0.16
% 8.41/3.01  CNF conversion       : 0.03
% 8.41/3.01  Main loop            : 1.89
% 8.41/3.01  Inferencing          : 0.46
% 8.41/3.01  Reduction            : 0.43
% 8.41/3.01  Demodulation         : 0.26
% 8.41/3.01  BG Simplification    : 0.06
% 8.41/3.01  Subsumption          : 0.85
% 8.41/3.01  Abstraction          : 0.06
% 8.41/3.01  MUC search           : 0.00
% 8.41/3.01  Cooper               : 0.00
% 8.41/3.01  Total                : 2.29
% 8.41/3.01  Index Insertion      : 0.00
% 8.41/3.01  Index Deletion       : 0.00
% 8.41/3.01  Index Matching       : 0.00
% 8.41/3.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
