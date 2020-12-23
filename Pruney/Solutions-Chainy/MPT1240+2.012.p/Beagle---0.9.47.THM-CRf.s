%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:47 EST 2020

% Result     : Theorem 9.35s
% Output     : CNFRefutation 9.53s
% Verified   : 
% Statistics : Number of formulae       :  176 ( 511 expanded)
%              Number of leaves         :   32 ( 175 expanded)
%              Depth                    :   17
%              Number of atoms          :  359 (1541 expanded)
%              Number of equality atoms :   21 (  50 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_127,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B,C] :
            ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
           => ( r2_hidden(B,k1_tops_1(A,C))
            <=> ? [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                  & v3_pre_topc(D,A)
                  & r1_tarski(D,C)
                  & r2_hidden(B,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_tops_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tops_1)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_108,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(c_38,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_36,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_6229,plain,(
    ! [A_473,B_474] :
      ( v3_pre_topc(k1_tops_1(A_473,B_474),A_473)
      | ~ m1_subset_1(B_474,k1_zfmisc_1(u1_struct_0(A_473)))
      | ~ l1_pre_topc(A_473)
      | ~ v2_pre_topc(A_473) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_6237,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_6229])).

tff(c_6242,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_6237])).

tff(c_60,plain,(
    ! [A_47,B_48] :
      ( r1_tarski(A_47,B_48)
      | ~ m1_subset_1(A_47,k1_zfmisc_1(B_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_68,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_60])).

tff(c_5882,plain,(
    ! [A_430,C_431,B_432] :
      ( r1_tarski(A_430,C_431)
      | ~ r1_tarski(B_432,C_431)
      | ~ r1_tarski(A_430,B_432) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_5889,plain,(
    ! [A_433] :
      ( r1_tarski(A_433,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_433,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_68,c_5882])).

tff(c_5794,plain,(
    ! [A_413,B_414] :
      ( v3_pre_topc(k1_tops_1(A_413,B_414),A_413)
      | ~ m1_subset_1(B_414,k1_zfmisc_1(u1_struct_0(A_413)))
      | ~ l1_pre_topc(A_413)
      | ~ v2_pre_topc(A_413) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_5802,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_5794])).

tff(c_5807,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_5802])).

tff(c_5089,plain,(
    ! [A_352,C_353,B_354] :
      ( r1_tarski(A_352,C_353)
      | ~ r1_tarski(B_354,C_353)
      | ~ r1_tarski(A_352,B_354) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_5106,plain,(
    ! [A_356] :
      ( r1_tarski(A_356,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_356,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_68,c_5089])).

tff(c_4997,plain,(
    ! [A_336,B_337] :
      ( v3_pre_topc(k1_tops_1(A_336,B_337),A_336)
      | ~ m1_subset_1(B_337,k1_zfmisc_1(u1_struct_0(A_336)))
      | ~ l1_pre_topc(A_336)
      | ~ v2_pre_topc(A_336) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_5005,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_4997])).

tff(c_5010,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_5005])).

tff(c_4422,plain,(
    ! [A_282,C_283,B_284] :
      ( r1_tarski(A_282,C_283)
      | ~ r1_tarski(B_284,C_283)
      | ~ r1_tarski(A_282,B_284) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4430,plain,(
    ! [A_282] :
      ( r1_tarski(A_282,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_282,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_68,c_4422])).

tff(c_50,plain,
    ( r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | r1_tarski('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_69,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_80,plain,(
    ! [A_54,C_55,B_56] :
      ( r1_tarski(A_54,C_55)
      | ~ r1_tarski(B_56,C_55)
      | ~ r1_tarski(A_54,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_88,plain,(
    ! [A_54] :
      ( r1_tarski(A_54,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_54,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_68,c_80])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_54,plain,
    ( r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | v3_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_70,plain,(
    v3_pre_topc('#skF_5','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_46,plain,
    ( r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | r2_hidden('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_71,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_58,plain,
    ( r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_108,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_101,plain,(
    ! [C_59,B_60,A_61] :
      ( r2_hidden(C_59,B_60)
      | ~ r2_hidden(C_59,A_61)
      | ~ r1_tarski(A_61,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_107,plain,(
    ! [B_60] :
      ( r2_hidden('#skF_3',B_60)
      | ~ r1_tarski('#skF_5',B_60) ) ),
    inference(resolution,[status(thm)],[c_71,c_101])).

tff(c_40,plain,(
    ! [D_44] :
      ( ~ r2_hidden('#skF_3',D_44)
      | ~ r1_tarski(D_44,'#skF_4')
      | ~ v3_pre_topc(D_44,'#skF_2')
      | ~ m1_subset_1(D_44,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_635,plain,(
    ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_643,plain,(
    ~ r1_tarski('#skF_5',k1_tops_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_107,c_635])).

tff(c_237,plain,(
    ! [A_75,B_76] :
      ( k3_subset_1(A_75,k3_subset_1(A_75,B_76)) = B_76
      | ~ m1_subset_1(B_76,k1_zfmisc_1(A_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_247,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_108,c_237])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(k3_subset_1(A_9,B_10),k1_zfmisc_1(A_9))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_552,plain,(
    ! [A_87,B_88] :
      ( k2_pre_topc(A_87,B_88) = B_88
      | ~ v4_pre_topc(B_88,A_87)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_559,plain,
    ( k2_pre_topc('#skF_2','#skF_5') = '#skF_5'
    | ~ v4_pre_topc('#skF_5','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_108,c_552])).

tff(c_570,plain,
    ( k2_pre_topc('#skF_2','#skF_5') = '#skF_5'
    | ~ v4_pre_topc('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_559])).

tff(c_576,plain,(
    ~ v4_pre_topc('#skF_5','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_570])).

tff(c_1055,plain,(
    ! [A_128,B_129] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_128),B_129),A_128)
      | ~ v3_pre_topc(B_129,A_128)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ l1_pre_topc(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1073,plain,
    ( v4_pre_topc('#skF_5','#skF_2')
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_1055])).

tff(c_1085,plain,
    ( v4_pre_topc('#skF_5','#skF_2')
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1073])).

tff(c_1086,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_576,c_1085])).

tff(c_2203,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1086])).

tff(c_2206,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_10,c_2203])).

tff(c_2213,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_2206])).

tff(c_2215,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_1086])).

tff(c_18,plain,(
    ! [B_17,A_15] :
      ( v4_pre_topc(B_17,A_15)
      | k2_pre_topc(A_15,B_17) != B_17
      | ~ v2_pre_topc(A_15)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2236,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),'#skF_2')
    | k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')) != k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')
    | ~ v2_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_2215,c_18])).

tff(c_2254,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),'#skF_2')
    | k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')) != k3_subset_1(u1_struct_0('#skF_2'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_38,c_2236])).

tff(c_4017,plain,(
    k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')) != k3_subset_1(u1_struct_0('#skF_2'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_2254])).

tff(c_28,plain,(
    ! [A_23,B_25] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_23),B_25),A_23)
      | ~ v3_pre_topc(B_25,A_23)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2692,plain,(
    ! [A_195,B_196] :
      ( k2_pre_topc(A_195,k3_subset_1(u1_struct_0(A_195),B_196)) = k3_subset_1(u1_struct_0(A_195),B_196)
      | ~ v4_pre_topc(k3_subset_1(u1_struct_0(A_195),B_196),A_195)
      | ~ l1_pre_topc(A_195)
      | ~ m1_subset_1(B_196,k1_zfmisc_1(u1_struct_0(A_195))) ) ),
    inference(resolution,[status(thm)],[c_10,c_552])).

tff(c_4018,plain,(
    ! [A_265,B_266] :
      ( k2_pre_topc(A_265,k3_subset_1(u1_struct_0(A_265),B_266)) = k3_subset_1(u1_struct_0(A_265),B_266)
      | ~ v3_pre_topc(B_266,A_265)
      | ~ m1_subset_1(B_266,k1_zfmisc_1(u1_struct_0(A_265)))
      | ~ l1_pre_topc(A_265) ) ),
    inference(resolution,[status(thm)],[c_28,c_2692])).

tff(c_4027,plain,
    ( k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')
    | ~ v3_pre_topc('#skF_5','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_108,c_4018])).

tff(c_4044,plain,(
    k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_70,c_4027])).

tff(c_4050,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4017,c_4044])).

tff(c_4052,plain,(
    k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_2254])).

tff(c_22,plain,(
    ! [A_18,B_20] :
      ( k3_subset_1(u1_struct_0(A_18),k2_pre_topc(A_18,k3_subset_1(u1_struct_0(A_18),B_20))) = k1_tops_1(A_18,B_20)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_4097,plain,
    ( k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')) = k1_tops_1('#skF_2','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4052,c_22])).

tff(c_4111,plain,(
    k1_tops_1('#skF_2','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_108,c_247,c_4097])).

tff(c_32,plain,(
    ! [A_29,B_33,C_35] :
      ( r1_tarski(k1_tops_1(A_29,B_33),k1_tops_1(A_29,C_35))
      | ~ r1_tarski(B_33,C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ l1_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_4184,plain,(
    ! [C_35] :
      ( r1_tarski('#skF_5',k1_tops_1('#skF_2',C_35))
      | ~ r1_tarski('#skF_5',C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4111,c_32])).

tff(c_4303,plain,(
    ! [C_274] :
      ( r1_tarski('#skF_5',k1_tops_1('#skF_2',C_274))
      | ~ r1_tarski('#skF_5',C_274)
      | ~ m1_subset_1(C_274,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_108,c_4184])).

tff(c_4323,plain,
    ( r1_tarski('#skF_5',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_4303])).

tff(c_4337,plain,(
    r1_tarski('#skF_5',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_4323])).

tff(c_4339,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_643,c_4337])).

tff(c_4375,plain,(
    ! [D_276] :
      ( ~ r2_hidden('#skF_3',D_276)
      | ~ r1_tarski(D_276,'#skF_4')
      | ~ v3_pre_topc(D_276,'#skF_2')
      | ~ m1_subset_1(D_276,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_4382,plain,
    ( ~ r2_hidden('#skF_3','#skF_5')
    | ~ r1_tarski('#skF_5','#skF_4')
    | ~ v3_pre_topc('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_108,c_4375])).

tff(c_4394,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_69,c_71,c_4382])).

tff(c_4396,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_4403,plain,(
    ~ r1_tarski('#skF_5',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_16,c_4396])).

tff(c_4406,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_88,c_4403])).

tff(c_4410,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_4406])).

tff(c_4411,plain,(
    r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_4443,plain,(
    ! [C_287,B_288,A_289] :
      ( r2_hidden(C_287,B_288)
      | ~ r2_hidden(C_287,A_289)
      | ~ r1_tarski(A_289,B_288) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4450,plain,(
    ! [B_290] :
      ( r2_hidden('#skF_3',B_290)
      | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),B_290) ) ),
    inference(resolution,[status(thm)],[c_4411,c_4443])).

tff(c_4459,plain,
    ( r2_hidden('#skF_3',u1_struct_0('#skF_2'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_4430,c_4450])).

tff(c_4506,plain,(
    ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_4459])).

tff(c_4571,plain,(
    ! [A_302,B_303] :
      ( r1_tarski(k1_tops_1(A_302,B_303),B_303)
      | ~ m1_subset_1(B_303,k1_zfmisc_1(u1_struct_0(A_302)))
      | ~ l1_pre_topc(A_302) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_4579,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_4571])).

tff(c_4584,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_4579])).

tff(c_4586,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4506,c_4584])).

tff(c_4588,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_4459])).

tff(c_4414,plain,(
    ! [A_279,B_280] :
      ( r2_hidden('#skF_1'(A_279,B_280),A_279)
      | r1_tarski(A_279,B_280) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4419,plain,(
    ! [A_279] : r1_tarski(A_279,A_279) ),
    inference(resolution,[status(thm)],[c_4414,c_4])).

tff(c_4439,plain,(
    ! [A_286] :
      ( r1_tarski(A_286,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_286,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_68,c_4422])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(A_6,C_8)
      | ~ r1_tarski(B_7,C_8)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4703,plain,(
    ! [A_314,A_315] :
      ( r1_tarski(A_314,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_314,A_315)
      | ~ r1_tarski(A_315,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4439,c_8])).

tff(c_4709,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),u1_struct_0('#skF_2'))
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_4588,c_4703])).

tff(c_4724,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4419,c_4709])).

tff(c_4412,plain,(
    ~ r2_hidden('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_44,plain,(
    ! [D_44] :
      ( ~ r2_hidden('#skF_3',D_44)
      | ~ r1_tarski(D_44,'#skF_4')
      | ~ v3_pre_topc(D_44,'#skF_2')
      | ~ m1_subset_1(D_44,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | r2_hidden('#skF_3','#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_4733,plain,(
    ! [D_316] :
      ( ~ r2_hidden('#skF_3',D_316)
      | ~ r1_tarski(D_316,'#skF_4')
      | ~ v3_pre_topc(D_316,'#skF_2')
      | ~ m1_subset_1(D_316,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_4412,c_44])).

tff(c_5021,plain,(
    ! [A_342] :
      ( ~ r2_hidden('#skF_3',A_342)
      | ~ r1_tarski(A_342,'#skF_4')
      | ~ v3_pre_topc(A_342,'#skF_2')
      | ~ r1_tarski(A_342,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_16,c_4733])).

tff(c_5037,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_4724,c_5021])).

tff(c_5062,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5010,c_4588,c_4411,c_5037])).

tff(c_5063,plain,(
    r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_5074,plain,(
    ! [C_348,B_349,A_350] :
      ( r2_hidden(C_348,B_349)
      | ~ r2_hidden(C_348,A_350)
      | ~ r1_tarski(A_350,B_349) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5080,plain,(
    ! [B_349] :
      ( r2_hidden('#skF_3',B_349)
      | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),B_349) ) ),
    inference(resolution,[status(thm)],[c_5063,c_5074])).

tff(c_5114,plain,
    ( r2_hidden('#skF_3',u1_struct_0('#skF_2'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_5106,c_5080])).

tff(c_5115,plain,(
    ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_5114])).

tff(c_5242,plain,(
    ! [A_369,B_370] :
      ( r1_tarski(k1_tops_1(A_369,B_370),B_370)
      | ~ m1_subset_1(B_370,k1_zfmisc_1(u1_struct_0(A_369)))
      | ~ l1_pre_topc(A_369) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_5250,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_5242])).

tff(c_5255,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_5250])).

tff(c_5257,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5115,c_5255])).

tff(c_5259,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_5114])).

tff(c_5066,plain,(
    ! [A_345,B_346] :
      ( r2_hidden('#skF_1'(A_345,B_346),A_345)
      | r1_tarski(A_345,B_346) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5071,plain,(
    ! [A_345] : r1_tarski(A_345,A_345) ),
    inference(resolution,[status(thm)],[c_5066,c_4])).

tff(c_5415,plain,(
    ! [A_385,A_386] :
      ( r1_tarski(A_385,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_385,A_386)
      | ~ r1_tarski(A_386,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_5106,c_8])).

tff(c_5421,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),u1_struct_0('#skF_2'))
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_5259,c_5415])).

tff(c_5436,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5071,c_5421])).

tff(c_5064,plain,(
    ~ v3_pre_topc('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_52,plain,(
    ! [D_44] :
      ( ~ r2_hidden('#skF_3',D_44)
      | ~ r1_tarski(D_44,'#skF_4')
      | ~ v3_pre_topc(D_44,'#skF_2')
      | ~ m1_subset_1(D_44,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v3_pre_topc('#skF_5','#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_5575,plain,(
    ! [D_394] :
      ( ~ r2_hidden('#skF_3',D_394)
      | ~ r1_tarski(D_394,'#skF_4')
      | ~ v3_pre_topc(D_394,'#skF_2')
      | ~ m1_subset_1(D_394,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_5064,c_52])).

tff(c_5814,plain,(
    ! [A_420] :
      ( ~ r2_hidden('#skF_3',A_420)
      | ~ r1_tarski(A_420,'#skF_4')
      | ~ v3_pre_topc(A_420,'#skF_2')
      | ~ r1_tarski(A_420,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_16,c_5575])).

tff(c_5830,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_5436,c_5814])).

tff(c_5855,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5807,c_5259,c_5063,c_5830])).

tff(c_5856,plain,(
    r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_5868,plain,(
    ! [C_426,B_427,A_428] :
      ( r2_hidden(C_426,B_427)
      | ~ r2_hidden(C_426,A_428)
      | ~ r1_tarski(A_428,B_427) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5874,plain,(
    ! [B_427] :
      ( r2_hidden('#skF_3',B_427)
      | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),B_427) ) ),
    inference(resolution,[status(thm)],[c_5856,c_5868])).

tff(c_5897,plain,
    ( r2_hidden('#skF_3',u1_struct_0('#skF_2'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_5889,c_5874])).

tff(c_5942,plain,(
    ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_5897])).

tff(c_5993,plain,(
    ! [A_447,B_448] :
      ( r1_tarski(k1_tops_1(A_447,B_448),B_448)
      | ~ m1_subset_1(B_448,k1_zfmisc_1(u1_struct_0(A_447)))
      | ~ l1_pre_topc(A_447) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_6001,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_5993])).

tff(c_6006,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_6001])).

tff(c_6008,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5942,c_6006])).

tff(c_6010,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_5897])).

tff(c_5860,plain,(
    ! [A_423,B_424] :
      ( r2_hidden('#skF_1'(A_423,B_424),A_423)
      | r1_tarski(A_423,B_424) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5865,plain,(
    ! [A_423] : r1_tarski(A_423,A_423) ),
    inference(resolution,[status(thm)],[c_5860,c_4])).

tff(c_6114,plain,(
    ! [A_460,A_461] :
      ( r1_tarski(A_460,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_460,A_461)
      | ~ r1_tarski(A_461,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_5889,c_8])).

tff(c_6118,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),u1_struct_0('#skF_2'))
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_6010,c_6114])).

tff(c_6128,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5865,c_6118])).

tff(c_5857,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_48,plain,(
    ! [D_44] :
      ( ~ r2_hidden('#skF_3',D_44)
      | ~ r1_tarski(D_44,'#skF_4')
      | ~ v3_pre_topc(D_44,'#skF_2')
      | ~ m1_subset_1(D_44,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | r1_tarski('#skF_5','#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_6494,plain,(
    ! [D_497] :
      ( ~ r2_hidden('#skF_3',D_497)
      | ~ r1_tarski(D_497,'#skF_4')
      | ~ v3_pre_topc(D_497,'#skF_2')
      | ~ m1_subset_1(D_497,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_5857,c_48])).

tff(c_6513,plain,(
    ! [A_500] :
      ( ~ r2_hidden('#skF_3',A_500)
      | ~ r1_tarski(A_500,'#skF_4')
      | ~ v3_pre_topc(A_500,'#skF_2')
      | ~ r1_tarski(A_500,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_16,c_6494])).

tff(c_6523,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_6128,c_6513])).

tff(c_6543,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6242,c_6010,c_5856,c_6523])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:26:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.35/3.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.44/3.31  
% 9.44/3.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.44/3.32  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 9.44/3.32  
% 9.44/3.32  %Foreground sorts:
% 9.44/3.32  
% 9.44/3.32  
% 9.44/3.32  %Background operators:
% 9.44/3.32  
% 9.44/3.32  
% 9.44/3.32  %Foreground operators:
% 9.44/3.32  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 9.44/3.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.44/3.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.44/3.32  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.44/3.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.44/3.32  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 9.44/3.32  tff('#skF_5', type, '#skF_5': $i).
% 9.44/3.32  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 9.44/3.32  tff('#skF_2', type, '#skF_2': $i).
% 9.44/3.32  tff('#skF_3', type, '#skF_3': $i).
% 9.44/3.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.44/3.32  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 9.44/3.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.44/3.32  tff('#skF_4', type, '#skF_4': $i).
% 9.44/3.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.44/3.32  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 9.44/3.32  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.44/3.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.44/3.32  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 9.44/3.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.44/3.32  
% 9.53/3.34  tff(f_127, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B, C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k1_tops_1(A, C)) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_tops_1)).
% 9.53/3.34  tff(f_80, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 9.53/3.34  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 9.53/3.34  tff(f_38, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 9.53/3.34  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 9.53/3.34  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 9.53/3.34  tff(f_42, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 9.53/3.34  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 9.53/3.34  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> v4_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_tops_1)).
% 9.53/3.34  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_1)).
% 9.53/3.34  tff(f_108, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 9.53/3.34  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 9.53/3.34  tff(c_38, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 9.53/3.34  tff(c_36, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 9.53/3.34  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 9.53/3.34  tff(c_6229, plain, (![A_473, B_474]: (v3_pre_topc(k1_tops_1(A_473, B_474), A_473) | ~m1_subset_1(B_474, k1_zfmisc_1(u1_struct_0(A_473))) | ~l1_pre_topc(A_473) | ~v2_pre_topc(A_473))), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.53/3.34  tff(c_6237, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_34, c_6229])).
% 9.53/3.34  tff(c_6242, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_6237])).
% 9.53/3.34  tff(c_60, plain, (![A_47, B_48]: (r1_tarski(A_47, B_48) | ~m1_subset_1(A_47, k1_zfmisc_1(B_48)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.53/3.34  tff(c_68, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_34, c_60])).
% 9.53/3.34  tff(c_5882, plain, (![A_430, C_431, B_432]: (r1_tarski(A_430, C_431) | ~r1_tarski(B_432, C_431) | ~r1_tarski(A_430, B_432))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.53/3.34  tff(c_5889, plain, (![A_433]: (r1_tarski(A_433, u1_struct_0('#skF_2')) | ~r1_tarski(A_433, '#skF_4'))), inference(resolution, [status(thm)], [c_68, c_5882])).
% 9.53/3.34  tff(c_5794, plain, (![A_413, B_414]: (v3_pre_topc(k1_tops_1(A_413, B_414), A_413) | ~m1_subset_1(B_414, k1_zfmisc_1(u1_struct_0(A_413))) | ~l1_pre_topc(A_413) | ~v2_pre_topc(A_413))), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.53/3.34  tff(c_5802, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_34, c_5794])).
% 9.53/3.34  tff(c_5807, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_5802])).
% 9.53/3.34  tff(c_5089, plain, (![A_352, C_353, B_354]: (r1_tarski(A_352, C_353) | ~r1_tarski(B_354, C_353) | ~r1_tarski(A_352, B_354))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.53/3.34  tff(c_5106, plain, (![A_356]: (r1_tarski(A_356, u1_struct_0('#skF_2')) | ~r1_tarski(A_356, '#skF_4'))), inference(resolution, [status(thm)], [c_68, c_5089])).
% 9.53/3.34  tff(c_4997, plain, (![A_336, B_337]: (v3_pre_topc(k1_tops_1(A_336, B_337), A_336) | ~m1_subset_1(B_337, k1_zfmisc_1(u1_struct_0(A_336))) | ~l1_pre_topc(A_336) | ~v2_pre_topc(A_336))), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.53/3.34  tff(c_5005, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_34, c_4997])).
% 9.53/3.34  tff(c_5010, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_5005])).
% 9.53/3.34  tff(c_4422, plain, (![A_282, C_283, B_284]: (r1_tarski(A_282, C_283) | ~r1_tarski(B_284, C_283) | ~r1_tarski(A_282, B_284))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.53/3.34  tff(c_4430, plain, (![A_282]: (r1_tarski(A_282, u1_struct_0('#skF_2')) | ~r1_tarski(A_282, '#skF_4'))), inference(resolution, [status(thm)], [c_68, c_4422])).
% 9.53/3.34  tff(c_50, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | r1_tarski('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 9.53/3.34  tff(c_69, plain, (r1_tarski('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_50])).
% 9.53/3.34  tff(c_80, plain, (![A_54, C_55, B_56]: (r1_tarski(A_54, C_55) | ~r1_tarski(B_56, C_55) | ~r1_tarski(A_54, B_56))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.53/3.34  tff(c_88, plain, (![A_54]: (r1_tarski(A_54, u1_struct_0('#skF_2')) | ~r1_tarski(A_54, '#skF_4'))), inference(resolution, [status(thm)], [c_68, c_80])).
% 9.53/3.34  tff(c_16, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.53/3.34  tff(c_54, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | v3_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 9.53/3.34  tff(c_70, plain, (v3_pre_topc('#skF_5', '#skF_2')), inference(splitLeft, [status(thm)], [c_54])).
% 9.53/3.34  tff(c_46, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | r2_hidden('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_127])).
% 9.53/3.34  tff(c_71, plain, (r2_hidden('#skF_3', '#skF_5')), inference(splitLeft, [status(thm)], [c_46])).
% 9.53/3.34  tff(c_58, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 9.53/3.34  tff(c_108, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_58])).
% 9.53/3.34  tff(c_101, plain, (![C_59, B_60, A_61]: (r2_hidden(C_59, B_60) | ~r2_hidden(C_59, A_61) | ~r1_tarski(A_61, B_60))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.53/3.34  tff(c_107, plain, (![B_60]: (r2_hidden('#skF_3', B_60) | ~r1_tarski('#skF_5', B_60))), inference(resolution, [status(thm)], [c_71, c_101])).
% 9.53/3.34  tff(c_40, plain, (![D_44]: (~r2_hidden('#skF_3', D_44) | ~r1_tarski(D_44, '#skF_4') | ~v3_pre_topc(D_44, '#skF_2') | ~m1_subset_1(D_44, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 9.53/3.34  tff(c_635, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_40])).
% 9.53/3.34  tff(c_643, plain, (~r1_tarski('#skF_5', k1_tops_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_107, c_635])).
% 9.53/3.34  tff(c_237, plain, (![A_75, B_76]: (k3_subset_1(A_75, k3_subset_1(A_75, B_76))=B_76 | ~m1_subset_1(B_76, k1_zfmisc_1(A_75)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.53/3.34  tff(c_247, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'))='#skF_5'), inference(resolution, [status(thm)], [c_108, c_237])).
% 9.53/3.34  tff(c_10, plain, (![A_9, B_10]: (m1_subset_1(k3_subset_1(A_9, B_10), k1_zfmisc_1(A_9)) | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.53/3.34  tff(c_552, plain, (![A_87, B_88]: (k2_pre_topc(A_87, B_88)=B_88 | ~v4_pre_topc(B_88, A_87) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.53/3.34  tff(c_559, plain, (k2_pre_topc('#skF_2', '#skF_5')='#skF_5' | ~v4_pre_topc('#skF_5', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_108, c_552])).
% 9.53/3.34  tff(c_570, plain, (k2_pre_topc('#skF_2', '#skF_5')='#skF_5' | ~v4_pre_topc('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_559])).
% 9.53/3.34  tff(c_576, plain, (~v4_pre_topc('#skF_5', '#skF_2')), inference(splitLeft, [status(thm)], [c_570])).
% 9.53/3.34  tff(c_1055, plain, (![A_128, B_129]: (v4_pre_topc(k3_subset_1(u1_struct_0(A_128), B_129), A_128) | ~v3_pre_topc(B_129, A_128) | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0(A_128))) | ~l1_pre_topc(A_128))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.53/3.34  tff(c_1073, plain, (v4_pre_topc('#skF_5', '#skF_2') | ~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'), '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_247, c_1055])).
% 9.53/3.34  tff(c_1085, plain, (v4_pre_topc('#skF_5', '#skF_2') | ~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'), '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1073])).
% 9.53/3.34  tff(c_1086, plain, (~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'), '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_576, c_1085])).
% 9.53/3.34  tff(c_2203, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_1086])).
% 9.53/3.34  tff(c_2206, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_10, c_2203])).
% 9.53/3.34  tff(c_2213, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_108, c_2206])).
% 9.53/3.34  tff(c_2215, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_1086])).
% 9.53/3.34  tff(c_18, plain, (![B_17, A_15]: (v4_pre_topc(B_17, A_15) | k2_pre_topc(A_15, B_17)!=B_17 | ~v2_pre_topc(A_15) | ~m1_subset_1(B_17, k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.53/3.34  tff(c_2236, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'), '#skF_2') | k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'))!=k3_subset_1(u1_struct_0('#skF_2'), '#skF_5') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_2215, c_18])).
% 9.53/3.34  tff(c_2254, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'), '#skF_2') | k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'))!=k3_subset_1(u1_struct_0('#skF_2'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_38, c_2236])).
% 9.53/3.34  tff(c_4017, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'))!=k3_subset_1(u1_struct_0('#skF_2'), '#skF_5')), inference(splitLeft, [status(thm)], [c_2254])).
% 9.53/3.34  tff(c_28, plain, (![A_23, B_25]: (v4_pre_topc(k3_subset_1(u1_struct_0(A_23), B_25), A_23) | ~v3_pre_topc(B_25, A_23) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.53/3.34  tff(c_2692, plain, (![A_195, B_196]: (k2_pre_topc(A_195, k3_subset_1(u1_struct_0(A_195), B_196))=k3_subset_1(u1_struct_0(A_195), B_196) | ~v4_pre_topc(k3_subset_1(u1_struct_0(A_195), B_196), A_195) | ~l1_pre_topc(A_195) | ~m1_subset_1(B_196, k1_zfmisc_1(u1_struct_0(A_195))))), inference(resolution, [status(thm)], [c_10, c_552])).
% 9.53/3.34  tff(c_4018, plain, (![A_265, B_266]: (k2_pre_topc(A_265, k3_subset_1(u1_struct_0(A_265), B_266))=k3_subset_1(u1_struct_0(A_265), B_266) | ~v3_pre_topc(B_266, A_265) | ~m1_subset_1(B_266, k1_zfmisc_1(u1_struct_0(A_265))) | ~l1_pre_topc(A_265))), inference(resolution, [status(thm)], [c_28, c_2692])).
% 9.53/3.34  tff(c_4027, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'))=k3_subset_1(u1_struct_0('#skF_2'), '#skF_5') | ~v3_pre_topc('#skF_5', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_108, c_4018])).
% 9.53/3.34  tff(c_4044, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'))=k3_subset_1(u1_struct_0('#skF_2'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_70, c_4027])).
% 9.53/3.34  tff(c_4050, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4017, c_4044])).
% 9.53/3.34  tff(c_4052, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'))=k3_subset_1(u1_struct_0('#skF_2'), '#skF_5')), inference(splitRight, [status(thm)], [c_2254])).
% 9.53/3.34  tff(c_22, plain, (![A_18, B_20]: (k3_subset_1(u1_struct_0(A_18), k2_pre_topc(A_18, k3_subset_1(u1_struct_0(A_18), B_20)))=k1_tops_1(A_18, B_20) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.53/3.34  tff(c_4097, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'))=k1_tops_1('#skF_2', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4052, c_22])).
% 9.53/3.34  tff(c_4111, plain, (k1_tops_1('#skF_2', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_108, c_247, c_4097])).
% 9.53/3.34  tff(c_32, plain, (![A_29, B_33, C_35]: (r1_tarski(k1_tops_1(A_29, B_33), k1_tops_1(A_29, C_35)) | ~r1_tarski(B_33, C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(u1_struct_0(A_29))) | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0(A_29))) | ~l1_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_108])).
% 9.53/3.34  tff(c_4184, plain, (![C_35]: (r1_tarski('#skF_5', k1_tops_1('#skF_2', C_35)) | ~r1_tarski('#skF_5', C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4111, c_32])).
% 9.53/3.34  tff(c_4303, plain, (![C_274]: (r1_tarski('#skF_5', k1_tops_1('#skF_2', C_274)) | ~r1_tarski('#skF_5', C_274) | ~m1_subset_1(C_274, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_108, c_4184])).
% 9.53/3.34  tff(c_4323, plain, (r1_tarski('#skF_5', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_34, c_4303])).
% 9.53/3.34  tff(c_4337, plain, (r1_tarski('#skF_5', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_4323])).
% 9.53/3.34  tff(c_4339, plain, $false, inference(negUnitSimplification, [status(thm)], [c_643, c_4337])).
% 9.53/3.34  tff(c_4375, plain, (![D_276]: (~r2_hidden('#skF_3', D_276) | ~r1_tarski(D_276, '#skF_4') | ~v3_pre_topc(D_276, '#skF_2') | ~m1_subset_1(D_276, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_40])).
% 9.53/3.34  tff(c_4382, plain, (~r2_hidden('#skF_3', '#skF_5') | ~r1_tarski('#skF_5', '#skF_4') | ~v3_pre_topc('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_108, c_4375])).
% 9.53/3.34  tff(c_4394, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_69, c_71, c_4382])).
% 9.53/3.34  tff(c_4396, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_58])).
% 9.53/3.34  tff(c_4403, plain, (~r1_tarski('#skF_5', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_16, c_4396])).
% 9.53/3.34  tff(c_4406, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_88, c_4403])).
% 9.53/3.34  tff(c_4410, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_69, c_4406])).
% 9.53/3.34  tff(c_4411, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_46])).
% 9.53/3.34  tff(c_4443, plain, (![C_287, B_288, A_289]: (r2_hidden(C_287, B_288) | ~r2_hidden(C_287, A_289) | ~r1_tarski(A_289, B_288))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.53/3.34  tff(c_4450, plain, (![B_290]: (r2_hidden('#skF_3', B_290) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), B_290))), inference(resolution, [status(thm)], [c_4411, c_4443])).
% 9.53/3.34  tff(c_4459, plain, (r2_hidden('#skF_3', u1_struct_0('#skF_2')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_4430, c_4450])).
% 9.53/3.34  tff(c_4506, plain, (~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_4459])).
% 9.53/3.34  tff(c_4571, plain, (![A_302, B_303]: (r1_tarski(k1_tops_1(A_302, B_303), B_303) | ~m1_subset_1(B_303, k1_zfmisc_1(u1_struct_0(A_302))) | ~l1_pre_topc(A_302))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.53/3.34  tff(c_4579, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_34, c_4571])).
% 9.53/3.34  tff(c_4584, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_4579])).
% 9.53/3.34  tff(c_4586, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4506, c_4584])).
% 9.53/3.34  tff(c_4588, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_4459])).
% 9.53/3.34  tff(c_4414, plain, (![A_279, B_280]: (r2_hidden('#skF_1'(A_279, B_280), A_279) | r1_tarski(A_279, B_280))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.53/3.34  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.53/3.34  tff(c_4419, plain, (![A_279]: (r1_tarski(A_279, A_279))), inference(resolution, [status(thm)], [c_4414, c_4])).
% 9.53/3.34  tff(c_4439, plain, (![A_286]: (r1_tarski(A_286, u1_struct_0('#skF_2')) | ~r1_tarski(A_286, '#skF_4'))), inference(resolution, [status(thm)], [c_68, c_4422])).
% 9.53/3.34  tff(c_8, plain, (![A_6, C_8, B_7]: (r1_tarski(A_6, C_8) | ~r1_tarski(B_7, C_8) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.53/3.34  tff(c_4703, plain, (![A_314, A_315]: (r1_tarski(A_314, u1_struct_0('#skF_2')) | ~r1_tarski(A_314, A_315) | ~r1_tarski(A_315, '#skF_4'))), inference(resolution, [status(thm)], [c_4439, c_8])).
% 9.53/3.34  tff(c_4709, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2')) | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_4588, c_4703])).
% 9.53/3.34  tff(c_4724, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4419, c_4709])).
% 9.53/3.34  tff(c_4412, plain, (~r2_hidden('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_46])).
% 9.53/3.34  tff(c_44, plain, (![D_44]: (~r2_hidden('#skF_3', D_44) | ~r1_tarski(D_44, '#skF_4') | ~v3_pre_topc(D_44, '#skF_2') | ~m1_subset_1(D_44, k1_zfmisc_1(u1_struct_0('#skF_2'))) | r2_hidden('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 9.53/3.34  tff(c_4733, plain, (![D_316]: (~r2_hidden('#skF_3', D_316) | ~r1_tarski(D_316, '#skF_4') | ~v3_pre_topc(D_316, '#skF_2') | ~m1_subset_1(D_316, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_4412, c_44])).
% 9.53/3.34  tff(c_5021, plain, (![A_342]: (~r2_hidden('#skF_3', A_342) | ~r1_tarski(A_342, '#skF_4') | ~v3_pre_topc(A_342, '#skF_2') | ~r1_tarski(A_342, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_16, c_4733])).
% 9.53/3.34  tff(c_5037, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_4724, c_5021])).
% 9.53/3.34  tff(c_5062, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5010, c_4588, c_4411, c_5037])).
% 9.53/3.34  tff(c_5063, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_54])).
% 9.53/3.34  tff(c_5074, plain, (![C_348, B_349, A_350]: (r2_hidden(C_348, B_349) | ~r2_hidden(C_348, A_350) | ~r1_tarski(A_350, B_349))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.53/3.34  tff(c_5080, plain, (![B_349]: (r2_hidden('#skF_3', B_349) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), B_349))), inference(resolution, [status(thm)], [c_5063, c_5074])).
% 9.53/3.34  tff(c_5114, plain, (r2_hidden('#skF_3', u1_struct_0('#skF_2')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_5106, c_5080])).
% 9.53/3.34  tff(c_5115, plain, (~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_5114])).
% 9.53/3.34  tff(c_5242, plain, (![A_369, B_370]: (r1_tarski(k1_tops_1(A_369, B_370), B_370) | ~m1_subset_1(B_370, k1_zfmisc_1(u1_struct_0(A_369))) | ~l1_pre_topc(A_369))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.53/3.34  tff(c_5250, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_34, c_5242])).
% 9.53/3.34  tff(c_5255, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_5250])).
% 9.53/3.34  tff(c_5257, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5115, c_5255])).
% 9.53/3.34  tff(c_5259, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_5114])).
% 9.53/3.34  tff(c_5066, plain, (![A_345, B_346]: (r2_hidden('#skF_1'(A_345, B_346), A_345) | r1_tarski(A_345, B_346))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.53/3.34  tff(c_5071, plain, (![A_345]: (r1_tarski(A_345, A_345))), inference(resolution, [status(thm)], [c_5066, c_4])).
% 9.53/3.34  tff(c_5415, plain, (![A_385, A_386]: (r1_tarski(A_385, u1_struct_0('#skF_2')) | ~r1_tarski(A_385, A_386) | ~r1_tarski(A_386, '#skF_4'))), inference(resolution, [status(thm)], [c_5106, c_8])).
% 9.53/3.34  tff(c_5421, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2')) | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_5259, c_5415])).
% 9.53/3.34  tff(c_5436, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_5071, c_5421])).
% 9.53/3.34  tff(c_5064, plain, (~v3_pre_topc('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_54])).
% 9.53/3.34  tff(c_52, plain, (![D_44]: (~r2_hidden('#skF_3', D_44) | ~r1_tarski(D_44, '#skF_4') | ~v3_pre_topc(D_44, '#skF_2') | ~m1_subset_1(D_44, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v3_pre_topc('#skF_5', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 9.53/3.34  tff(c_5575, plain, (![D_394]: (~r2_hidden('#skF_3', D_394) | ~r1_tarski(D_394, '#skF_4') | ~v3_pre_topc(D_394, '#skF_2') | ~m1_subset_1(D_394, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_5064, c_52])).
% 9.53/3.34  tff(c_5814, plain, (![A_420]: (~r2_hidden('#skF_3', A_420) | ~r1_tarski(A_420, '#skF_4') | ~v3_pre_topc(A_420, '#skF_2') | ~r1_tarski(A_420, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_16, c_5575])).
% 9.53/3.34  tff(c_5830, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_5436, c_5814])).
% 9.53/3.34  tff(c_5855, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5807, c_5259, c_5063, c_5830])).
% 9.53/3.34  tff(c_5856, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_50])).
% 9.53/3.34  tff(c_5868, plain, (![C_426, B_427, A_428]: (r2_hidden(C_426, B_427) | ~r2_hidden(C_426, A_428) | ~r1_tarski(A_428, B_427))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.53/3.34  tff(c_5874, plain, (![B_427]: (r2_hidden('#skF_3', B_427) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), B_427))), inference(resolution, [status(thm)], [c_5856, c_5868])).
% 9.53/3.34  tff(c_5897, plain, (r2_hidden('#skF_3', u1_struct_0('#skF_2')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_5889, c_5874])).
% 9.53/3.34  tff(c_5942, plain, (~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_5897])).
% 9.53/3.34  tff(c_5993, plain, (![A_447, B_448]: (r1_tarski(k1_tops_1(A_447, B_448), B_448) | ~m1_subset_1(B_448, k1_zfmisc_1(u1_struct_0(A_447))) | ~l1_pre_topc(A_447))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.53/3.34  tff(c_6001, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_34, c_5993])).
% 9.53/3.34  tff(c_6006, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_6001])).
% 9.53/3.34  tff(c_6008, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5942, c_6006])).
% 9.53/3.34  tff(c_6010, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_5897])).
% 9.53/3.34  tff(c_5860, plain, (![A_423, B_424]: (r2_hidden('#skF_1'(A_423, B_424), A_423) | r1_tarski(A_423, B_424))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.53/3.34  tff(c_5865, plain, (![A_423]: (r1_tarski(A_423, A_423))), inference(resolution, [status(thm)], [c_5860, c_4])).
% 9.53/3.34  tff(c_6114, plain, (![A_460, A_461]: (r1_tarski(A_460, u1_struct_0('#skF_2')) | ~r1_tarski(A_460, A_461) | ~r1_tarski(A_461, '#skF_4'))), inference(resolution, [status(thm)], [c_5889, c_8])).
% 9.53/3.34  tff(c_6118, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2')) | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_6010, c_6114])).
% 9.53/3.34  tff(c_6128, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_5865, c_6118])).
% 9.53/3.34  tff(c_5857, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_50])).
% 9.53/3.34  tff(c_48, plain, (![D_44]: (~r2_hidden('#skF_3', D_44) | ~r1_tarski(D_44, '#skF_4') | ~v3_pre_topc(D_44, '#skF_2') | ~m1_subset_1(D_44, k1_zfmisc_1(u1_struct_0('#skF_2'))) | r1_tarski('#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 9.53/3.34  tff(c_6494, plain, (![D_497]: (~r2_hidden('#skF_3', D_497) | ~r1_tarski(D_497, '#skF_4') | ~v3_pre_topc(D_497, '#skF_2') | ~m1_subset_1(D_497, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_5857, c_48])).
% 9.53/3.34  tff(c_6513, plain, (![A_500]: (~r2_hidden('#skF_3', A_500) | ~r1_tarski(A_500, '#skF_4') | ~v3_pre_topc(A_500, '#skF_2') | ~r1_tarski(A_500, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_16, c_6494])).
% 9.53/3.34  tff(c_6523, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_6128, c_6513])).
% 9.53/3.34  tff(c_6543, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6242, c_6010, c_5856, c_6523])).
% 9.53/3.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.53/3.34  
% 9.53/3.34  Inference rules
% 9.53/3.34  ----------------------
% 9.53/3.34  #Ref     : 0
% 9.53/3.34  #Sup     : 1484
% 9.53/3.34  #Fact    : 0
% 9.53/3.34  #Define  : 0
% 9.53/3.34  #Split   : 39
% 9.53/3.34  #Chain   : 0
% 9.53/3.34  #Close   : 0
% 9.53/3.34  
% 9.53/3.34  Ordering : KBO
% 9.53/3.34  
% 9.53/3.34  Simplification rules
% 9.53/3.34  ----------------------
% 9.53/3.34  #Subsume      : 359
% 9.53/3.34  #Demod        : 838
% 9.53/3.34  #Tautology    : 399
% 9.53/3.34  #SimpNegUnit  : 37
% 9.53/3.34  #BackRed      : 18
% 9.53/3.34  
% 9.53/3.34  #Partial instantiations: 0
% 9.53/3.34  #Strategies tried      : 1
% 9.53/3.34  
% 9.53/3.34  Timing (in seconds)
% 9.53/3.34  ----------------------
% 9.53/3.35  Preprocessing        : 0.51
% 9.53/3.35  Parsing              : 0.28
% 9.53/3.35  CNF conversion       : 0.04
% 9.53/3.35  Main loop            : 1.94
% 9.53/3.35  Inferencing          : 0.62
% 9.53/3.35  Reduction            : 0.60
% 9.53/3.35  Demodulation         : 0.42
% 9.53/3.35  BG Simplification    : 0.06
% 9.53/3.35  Subsumption          : 0.51
% 9.53/3.35  Abstraction          : 0.07
% 9.53/3.35  MUC search           : 0.00
% 9.53/3.35  Cooper               : 0.00
% 9.53/3.35  Total                : 2.52
% 9.53/3.35  Index Insertion      : 0.00
% 9.53/3.35  Index Deletion       : 0.00
% 9.53/3.35  Index Matching       : 0.00
% 9.53/3.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
