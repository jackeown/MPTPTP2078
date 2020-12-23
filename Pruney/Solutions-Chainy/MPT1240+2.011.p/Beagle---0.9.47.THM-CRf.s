%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:46 EST 2020

% Result     : Theorem 6.09s
% Output     : CNFRefutation 6.09s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 332 expanded)
%              Number of leaves         :   31 ( 121 expanded)
%              Depth                    :   17
%              Number of atoms          :  312 (1127 expanded)
%              Number of equality atoms :   16 (  42 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

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

tff(f_123,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_tops_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_104,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(c_34,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_32,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_4132,plain,(
    ! [A_464,B_465] :
      ( v3_pre_topc(k1_tops_1(A_464,B_465),A_464)
      | ~ m1_subset_1(B_465,k1_zfmisc_1(u1_struct_0(A_464)))
      | ~ l1_pre_topc(A_464)
      | ~ v2_pre_topc(A_464) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_4139,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_4132])).

tff(c_4144,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_4139])).

tff(c_3428,plain,(
    ! [A_397,B_398] :
      ( r1_tarski(k1_tops_1(A_397,B_398),B_398)
      | ~ m1_subset_1(B_398,k1_zfmisc_1(u1_struct_0(A_397)))
      | ~ l1_pre_topc(A_397) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_3433,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_3428])).

tff(c_3437,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_3433])).

tff(c_2422,plain,(
    ! [A_297,B_298] :
      ( v3_pre_topc(k1_tops_1(A_297,B_298),A_297)
      | ~ m1_subset_1(B_298,k1_zfmisc_1(u1_struct_0(A_297)))
      | ~ l1_pre_topc(A_297)
      | ~ v2_pre_topc(A_297) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2427,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_2422])).

tff(c_2431,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_2427])).

tff(c_2408,plain,(
    ! [A_295,B_296] :
      ( r1_tarski(k1_tops_1(A_295,B_296),B_296)
      | ~ m1_subset_1(B_296,k1_zfmisc_1(u1_struct_0(A_295)))
      | ~ l1_pre_topc(A_295) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2413,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_2408])).

tff(c_2417,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2413])).

tff(c_1891,plain,(
    ! [A_231,B_232] :
      ( v3_pre_topc(k1_tops_1(A_231,B_232),A_231)
      | ~ m1_subset_1(B_232,k1_zfmisc_1(u1_struct_0(A_231)))
      | ~ l1_pre_topc(A_231)
      | ~ v2_pre_topc(A_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1898,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_1891])).

tff(c_1903,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_1898])).

tff(c_1822,plain,(
    ! [A_222,B_223] :
      ( r1_tarski(k1_tops_1(A_222,B_223),B_223)
      | ~ m1_subset_1(B_223,k1_zfmisc_1(u1_struct_0(A_222)))
      | ~ l1_pre_topc(A_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1827,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_1822])).

tff(c_1831,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1827])).

tff(c_1359,plain,(
    ! [A_166,B_167] :
      ( v3_pre_topc(k1_tops_1(A_166,B_167),A_166)
      | ~ m1_subset_1(B_167,k1_zfmisc_1(u1_struct_0(A_166)))
      | ~ l1_pre_topc(A_166)
      | ~ v2_pre_topc(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1364,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_1359])).

tff(c_1368,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_1364])).

tff(c_1322,plain,(
    ! [A_162,B_163] :
      ( r1_tarski(k1_tops_1(A_162,B_163),B_163)
      | ~ m1_subset_1(B_163,k1_zfmisc_1(u1_struct_0(A_162)))
      | ~ l1_pre_topc(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1327,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_1322])).

tff(c_1331,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1327])).

tff(c_50,plain,
    ( r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | v3_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_55,plain,(
    v3_pre_topc('#skF_5','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_46,plain,
    ( r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | r1_tarski('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_56,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_42,plain,
    ( r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | r2_hidden('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_58,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_54,plain,
    ( r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_59,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_67,plain,(
    ! [C_47,B_48,A_49] :
      ( r2_hidden(C_47,B_48)
      | ~ r2_hidden(C_47,A_49)
      | ~ r1_tarski(A_49,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_72,plain,(
    ! [B_48] :
      ( r2_hidden('#skF_3',B_48)
      | ~ r1_tarski('#skF_5',B_48) ) ),
    inference(resolution,[status(thm)],[c_58,c_67])).

tff(c_36,plain,(
    ! [D_41] :
      ( ~ r2_hidden('#skF_3',D_41)
      | ~ r1_tarski(D_41,'#skF_4')
      | ~ v3_pre_topc(D_41,'#skF_2')
      | ~ m1_subset_1(D_41,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_352,plain,(
    ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_360,plain,(
    ~ r1_tarski('#skF_5',k1_tops_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_72,c_352])).

tff(c_74,plain,(
    ! [A_50,B_51] :
      ( k3_subset_1(A_50,k3_subset_1(A_50,B_51)) = B_51
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_79,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_59,c_74])).

tff(c_24,plain,(
    ! [A_20,B_22] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_20),B_22),A_20)
      | ~ v3_pre_topc(B_22,A_20)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(k3_subset_1(A_6,B_7),k1_zfmisc_1(A_6))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_196,plain,(
    ! [A_69,B_70] :
      ( k2_pre_topc(A_69,B_70) = B_70
      | ~ v4_pre_topc(B_70,A_69)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_206,plain,
    ( k2_pre_topc('#skF_2','#skF_5') = '#skF_5'
    | ~ v4_pre_topc('#skF_5','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_59,c_196])).

tff(c_214,plain,
    ( k2_pre_topc('#skF_2','#skF_5') = '#skF_5'
    | ~ v4_pre_topc('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_206])).

tff(c_230,plain,(
    ~ v4_pre_topc('#skF_5','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_214])).

tff(c_218,plain,(
    ! [A_71,B_72] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_71),B_72),A_71)
      | ~ v3_pre_topc(B_72,A_71)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_221,plain,
    ( v4_pre_topc('#skF_5','#skF_2')
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_218])).

tff(c_226,plain,
    ( v4_pre_topc('#skF_5','#skF_2')
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_221])).

tff(c_874,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_230,c_226])).

tff(c_875,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_874])).

tff(c_878,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_8,c_875])).

tff(c_882,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_878])).

tff(c_884,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_874])).

tff(c_14,plain,(
    ! [A_10,B_12] :
      ( k2_pre_topc(A_10,B_12) = B_12
      | ~ v4_pre_topc(B_12,A_10)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_899,plain,
    ( k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_884,c_14])).

tff(c_914,plain,
    ( k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_899])).

tff(c_1041,plain,(
    ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_914])).

tff(c_1044,plain,
    ( ~ v3_pre_topc('#skF_5','#skF_2')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_1041])).

tff(c_1048,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_59,c_55,c_1044])).

tff(c_1049,plain,(
    k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_914])).

tff(c_16,plain,(
    ! [A_13,B_15] :
      ( k3_subset_1(u1_struct_0(A_13),k2_pre_topc(A_13,k3_subset_1(u1_struct_0(A_13),B_15))) = k1_tops_1(A_13,B_15)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1088,plain,
    ( k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')) = k1_tops_1('#skF_2','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1049,c_16])).

tff(c_1092,plain,(
    k1_tops_1('#skF_2','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_59,c_79,c_1088])).

tff(c_28,plain,(
    ! [A_26,B_30,C_32] :
      ( r1_tarski(k1_tops_1(A_26,B_30),k1_tops_1(A_26,C_32))
      | ~ r1_tarski(B_30,C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ m1_subset_1(B_30,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1121,plain,(
    ! [C_32] :
      ( r1_tarski('#skF_5',k1_tops_1('#skF_2',C_32))
      | ~ r1_tarski('#skF_5',C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1092,c_28])).

tff(c_1162,plain,(
    ! [C_139] :
      ( r1_tarski('#skF_5',k1_tops_1('#skF_2',C_139))
      | ~ r1_tarski('#skF_5',C_139)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_59,c_1121])).

tff(c_1182,plain,
    ( r1_tarski('#skF_5',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_1162])).

tff(c_1198,plain,(
    r1_tarski('#skF_5',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1182])).

tff(c_1200,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_360,c_1198])).

tff(c_1218,plain,(
    ! [D_141] :
      ( ~ r2_hidden('#skF_3',D_141)
      | ~ r1_tarski(D_141,'#skF_4')
      | ~ v3_pre_topc(D_141,'#skF_2')
      | ~ m1_subset_1(D_141,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_1229,plain,
    ( ~ r2_hidden('#skF_3','#skF_5')
    | ~ r1_tarski('#skF_5','#skF_4')
    | ~ v3_pre_topc('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_59,c_1218])).

tff(c_1240,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_56,c_58,c_1229])).

tff(c_1241,plain,(
    r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_18,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(k1_tops_1(A_16,B_17),k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1242,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_52,plain,(
    ! [D_41] :
      ( ~ r2_hidden('#skF_3',D_41)
      | ~ r1_tarski(D_41,'#skF_4')
      | ~ v3_pre_topc(D_41,'#skF_2')
      | ~ m1_subset_1(D_41,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1468,plain,(
    ! [D_183] :
      ( ~ r2_hidden('#skF_3',D_183)
      | ~ r1_tarski(D_183,'#skF_4')
      | ~ v3_pre_topc(D_183,'#skF_2')
      | ~ m1_subset_1(D_183,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1242,c_52])).

tff(c_1472,plain,(
    ! [B_17] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_17))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_17),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_17),'#skF_2')
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_18,c_1468])).

tff(c_1733,plain,(
    ! [B_206] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_206))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_206),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_206),'#skF_2')
      | ~ m1_subset_1(B_206,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1472])).

tff(c_1747,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_1733])).

tff(c_1758,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1368,c_1331,c_1241,c_1747])).

tff(c_1759,plain,(
    r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_1832,plain,(
    ! [A_224,B_225] :
      ( m1_subset_1(k1_tops_1(A_224,B_225),k1_zfmisc_1(u1_struct_0(A_224)))
      | ~ m1_subset_1(B_225,k1_zfmisc_1(u1_struct_0(A_224)))
      | ~ l1_pre_topc(A_224) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1760,plain,(
    ~ r2_hidden('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_40,plain,(
    ! [D_41] :
      ( ~ r2_hidden('#skF_3',D_41)
      | ~ r1_tarski(D_41,'#skF_4')
      | ~ v3_pre_topc(D_41,'#skF_2')
      | ~ m1_subset_1(D_41,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | r2_hidden('#skF_3','#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1791,plain,(
    ! [D_41] :
      ( ~ r2_hidden('#skF_3',D_41)
      | ~ r1_tarski(D_41,'#skF_4')
      | ~ v3_pre_topc(D_41,'#skF_2')
      | ~ m1_subset_1(D_41,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1760,c_40])).

tff(c_1838,plain,(
    ! [B_225] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_225))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_225),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_225),'#skF_2')
      | ~ m1_subset_1(B_225,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1832,c_1791])).

tff(c_2331,plain,(
    ! [B_278] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_278))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_278),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_278),'#skF_2')
      | ~ m1_subset_1(B_278,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1838])).

tff(c_2345,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_2331])).

tff(c_2356,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1903,c_1831,c_1759,c_2345])).

tff(c_2357,plain,(
    r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_2358,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_44,plain,(
    ! [D_41] :
      ( ~ r2_hidden('#skF_3',D_41)
      | ~ r1_tarski(D_41,'#skF_4')
      | ~ v3_pre_topc(D_41,'#skF_2')
      | ~ m1_subset_1(D_41,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | r1_tarski('#skF_5','#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_3038,plain,(
    ! [D_357] :
      ( ~ r2_hidden('#skF_3',D_357)
      | ~ r1_tarski(D_357,'#skF_4')
      | ~ v3_pre_topc(D_357,'#skF_2')
      | ~ m1_subset_1(D_357,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2358,c_44])).

tff(c_3042,plain,(
    ! [B_17] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_17))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_17),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_17),'#skF_2')
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_18,c_3038])).

tff(c_3350,plain,(
    ! [B_380] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_380))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_380),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_380),'#skF_2')
      | ~ m1_subset_1(B_380,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_3042])).

tff(c_3364,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_3350])).

tff(c_3375,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2431,c_2417,c_2357,c_3364])).

tff(c_3376,plain,(
    r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_3377,plain,(
    ~ v3_pre_topc('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_48,plain,(
    ! [D_41] :
      ( ~ r2_hidden('#skF_3',D_41)
      | ~ r1_tarski(D_41,'#skF_4')
      | ~ v3_pre_topc(D_41,'#skF_2')
      | ~ m1_subset_1(D_41,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v3_pre_topc('#skF_5','#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_4679,plain,(
    ! [D_516] :
      ( ~ r2_hidden('#skF_3',D_516)
      | ~ r1_tarski(D_516,'#skF_4')
      | ~ v3_pre_topc(D_516,'#skF_2')
      | ~ m1_subset_1(D_516,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_3377,c_48])).

tff(c_4683,plain,(
    ! [B_17] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_17))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_17),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_17),'#skF_2')
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_18,c_4679])).

tff(c_5056,plain,(
    ! [B_550] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_550))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_550),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_550),'#skF_2')
      | ~ m1_subset_1(B_550,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_4683])).

tff(c_5070,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_5056])).

tff(c_5081,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4144,c_3437,c_3376,c_5070])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:42:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.09/2.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.09/2.18  
% 6.09/2.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.09/2.18  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 6.09/2.18  
% 6.09/2.18  %Foreground sorts:
% 6.09/2.18  
% 6.09/2.18  
% 6.09/2.18  %Background operators:
% 6.09/2.18  
% 6.09/2.18  
% 6.09/2.18  %Foreground operators:
% 6.09/2.18  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 6.09/2.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.09/2.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.09/2.18  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.09/2.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.09/2.18  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 6.09/2.18  tff('#skF_5', type, '#skF_5': $i).
% 6.09/2.18  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 6.09/2.18  tff('#skF_2', type, '#skF_2': $i).
% 6.09/2.18  tff('#skF_3', type, '#skF_3': $i).
% 6.09/2.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.09/2.18  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 6.09/2.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.09/2.18  tff('#skF_4', type, '#skF_4': $i).
% 6.09/2.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.09/2.18  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.09/2.19  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.09/2.19  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.09/2.19  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 6.09/2.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.09/2.19  
% 6.09/2.21  tff(f_123, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B, C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k1_tops_1(A, C)) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_tops_1)).
% 6.09/2.21  tff(f_76, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 6.09/2.21  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 6.09/2.21  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.09/2.21  tff(f_40, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 6.09/2.21  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> v4_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_tops_1)).
% 6.09/2.21  tff(f_36, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 6.09/2.21  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 6.09/2.21  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 6.09/2.21  tff(f_104, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 6.09/2.21  tff(f_68, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 6.09/2.21  tff(c_34, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.09/2.21  tff(c_32, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.09/2.21  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.09/2.21  tff(c_4132, plain, (![A_464, B_465]: (v3_pre_topc(k1_tops_1(A_464, B_465), A_464) | ~m1_subset_1(B_465, k1_zfmisc_1(u1_struct_0(A_464))) | ~l1_pre_topc(A_464) | ~v2_pre_topc(A_464))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.09/2.21  tff(c_4139, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_4132])).
% 6.09/2.21  tff(c_4144, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_4139])).
% 6.09/2.21  tff(c_3428, plain, (![A_397, B_398]: (r1_tarski(k1_tops_1(A_397, B_398), B_398) | ~m1_subset_1(B_398, k1_zfmisc_1(u1_struct_0(A_397))) | ~l1_pre_topc(A_397))), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.09/2.21  tff(c_3433, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_3428])).
% 6.09/2.21  tff(c_3437, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_3433])).
% 6.09/2.21  tff(c_2422, plain, (![A_297, B_298]: (v3_pre_topc(k1_tops_1(A_297, B_298), A_297) | ~m1_subset_1(B_298, k1_zfmisc_1(u1_struct_0(A_297))) | ~l1_pre_topc(A_297) | ~v2_pre_topc(A_297))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.09/2.21  tff(c_2427, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_2422])).
% 6.09/2.21  tff(c_2431, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_2427])).
% 6.09/2.21  tff(c_2408, plain, (![A_295, B_296]: (r1_tarski(k1_tops_1(A_295, B_296), B_296) | ~m1_subset_1(B_296, k1_zfmisc_1(u1_struct_0(A_295))) | ~l1_pre_topc(A_295))), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.09/2.21  tff(c_2413, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_2408])).
% 6.09/2.21  tff(c_2417, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2413])).
% 6.09/2.21  tff(c_1891, plain, (![A_231, B_232]: (v3_pre_topc(k1_tops_1(A_231, B_232), A_231) | ~m1_subset_1(B_232, k1_zfmisc_1(u1_struct_0(A_231))) | ~l1_pre_topc(A_231) | ~v2_pre_topc(A_231))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.09/2.21  tff(c_1898, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_1891])).
% 6.09/2.21  tff(c_1903, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_1898])).
% 6.09/2.21  tff(c_1822, plain, (![A_222, B_223]: (r1_tarski(k1_tops_1(A_222, B_223), B_223) | ~m1_subset_1(B_223, k1_zfmisc_1(u1_struct_0(A_222))) | ~l1_pre_topc(A_222))), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.09/2.21  tff(c_1827, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_1822])).
% 6.09/2.21  tff(c_1831, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1827])).
% 6.09/2.21  tff(c_1359, plain, (![A_166, B_167]: (v3_pre_topc(k1_tops_1(A_166, B_167), A_166) | ~m1_subset_1(B_167, k1_zfmisc_1(u1_struct_0(A_166))) | ~l1_pre_topc(A_166) | ~v2_pre_topc(A_166))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.09/2.21  tff(c_1364, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_1359])).
% 6.09/2.21  tff(c_1368, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_1364])).
% 6.09/2.21  tff(c_1322, plain, (![A_162, B_163]: (r1_tarski(k1_tops_1(A_162, B_163), B_163) | ~m1_subset_1(B_163, k1_zfmisc_1(u1_struct_0(A_162))) | ~l1_pre_topc(A_162))), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.09/2.21  tff(c_1327, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_1322])).
% 6.09/2.21  tff(c_1331, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1327])).
% 6.09/2.21  tff(c_50, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | v3_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.09/2.21  tff(c_55, plain, (v3_pre_topc('#skF_5', '#skF_2')), inference(splitLeft, [status(thm)], [c_50])).
% 6.09/2.21  tff(c_46, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | r1_tarski('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.09/2.21  tff(c_56, plain, (r1_tarski('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_46])).
% 6.09/2.21  tff(c_42, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | r2_hidden('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.09/2.21  tff(c_58, plain, (r2_hidden('#skF_3', '#skF_5')), inference(splitLeft, [status(thm)], [c_42])).
% 6.09/2.21  tff(c_54, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.09/2.21  tff(c_59, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_54])).
% 6.09/2.21  tff(c_67, plain, (![C_47, B_48, A_49]: (r2_hidden(C_47, B_48) | ~r2_hidden(C_47, A_49) | ~r1_tarski(A_49, B_48))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.09/2.21  tff(c_72, plain, (![B_48]: (r2_hidden('#skF_3', B_48) | ~r1_tarski('#skF_5', B_48))), inference(resolution, [status(thm)], [c_58, c_67])).
% 6.09/2.21  tff(c_36, plain, (![D_41]: (~r2_hidden('#skF_3', D_41) | ~r1_tarski(D_41, '#skF_4') | ~v3_pre_topc(D_41, '#skF_2') | ~m1_subset_1(D_41, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.09/2.21  tff(c_352, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_36])).
% 6.09/2.21  tff(c_360, plain, (~r1_tarski('#skF_5', k1_tops_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_72, c_352])).
% 6.09/2.21  tff(c_74, plain, (![A_50, B_51]: (k3_subset_1(A_50, k3_subset_1(A_50, B_51))=B_51 | ~m1_subset_1(B_51, k1_zfmisc_1(A_50)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.09/2.21  tff(c_79, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'))='#skF_5'), inference(resolution, [status(thm)], [c_59, c_74])).
% 6.09/2.21  tff(c_24, plain, (![A_20, B_22]: (v4_pre_topc(k3_subset_1(u1_struct_0(A_20), B_22), A_20) | ~v3_pre_topc(B_22, A_20) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.09/2.21  tff(c_8, plain, (![A_6, B_7]: (m1_subset_1(k3_subset_1(A_6, B_7), k1_zfmisc_1(A_6)) | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.09/2.21  tff(c_196, plain, (![A_69, B_70]: (k2_pre_topc(A_69, B_70)=B_70 | ~v4_pre_topc(B_70, A_69) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.09/2.21  tff(c_206, plain, (k2_pre_topc('#skF_2', '#skF_5')='#skF_5' | ~v4_pre_topc('#skF_5', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_59, c_196])).
% 6.09/2.21  tff(c_214, plain, (k2_pre_topc('#skF_2', '#skF_5')='#skF_5' | ~v4_pre_topc('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_206])).
% 6.09/2.21  tff(c_230, plain, (~v4_pre_topc('#skF_5', '#skF_2')), inference(splitLeft, [status(thm)], [c_214])).
% 6.09/2.21  tff(c_218, plain, (![A_71, B_72]: (v4_pre_topc(k3_subset_1(u1_struct_0(A_71), B_72), A_71) | ~v3_pre_topc(B_72, A_71) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.09/2.21  tff(c_221, plain, (v4_pre_topc('#skF_5', '#skF_2') | ~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'), '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_79, c_218])).
% 6.09/2.21  tff(c_226, plain, (v4_pre_topc('#skF_5', '#skF_2') | ~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'), '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_221])).
% 6.09/2.21  tff(c_874, plain, (~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'), '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_230, c_226])).
% 6.09/2.21  tff(c_875, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_874])).
% 6.09/2.21  tff(c_878, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_8, c_875])).
% 6.09/2.21  tff(c_882, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_59, c_878])).
% 6.09/2.21  tff(c_884, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_874])).
% 6.09/2.21  tff(c_14, plain, (![A_10, B_12]: (k2_pre_topc(A_10, B_12)=B_12 | ~v4_pre_topc(B_12, A_10) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0(A_10))) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.09/2.21  tff(c_899, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'))=k3_subset_1(u1_struct_0('#skF_2'), '#skF_5') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_884, c_14])).
% 6.09/2.21  tff(c_914, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'))=k3_subset_1(u1_struct_0('#skF_2'), '#skF_5') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_899])).
% 6.09/2.21  tff(c_1041, plain, (~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'), '#skF_2')), inference(splitLeft, [status(thm)], [c_914])).
% 6.09/2.21  tff(c_1044, plain, (~v3_pre_topc('#skF_5', '#skF_2') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24, c_1041])).
% 6.09/2.21  tff(c_1048, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_59, c_55, c_1044])).
% 6.09/2.21  tff(c_1049, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'))=k3_subset_1(u1_struct_0('#skF_2'), '#skF_5')), inference(splitRight, [status(thm)], [c_914])).
% 6.09/2.21  tff(c_16, plain, (![A_13, B_15]: (k3_subset_1(u1_struct_0(A_13), k2_pre_topc(A_13, k3_subset_1(u1_struct_0(A_13), B_15)))=k1_tops_1(A_13, B_15) | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0(A_13))) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.09/2.21  tff(c_1088, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'))=k1_tops_1('#skF_2', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1049, c_16])).
% 6.09/2.21  tff(c_1092, plain, (k1_tops_1('#skF_2', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_59, c_79, c_1088])).
% 6.09/2.21  tff(c_28, plain, (![A_26, B_30, C_32]: (r1_tarski(k1_tops_1(A_26, B_30), k1_tops_1(A_26, C_32)) | ~r1_tarski(B_30, C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(u1_struct_0(A_26))) | ~m1_subset_1(B_30, k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.09/2.21  tff(c_1121, plain, (![C_32]: (r1_tarski('#skF_5', k1_tops_1('#skF_2', C_32)) | ~r1_tarski('#skF_5', C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1092, c_28])).
% 6.09/2.21  tff(c_1162, plain, (![C_139]: (r1_tarski('#skF_5', k1_tops_1('#skF_2', C_139)) | ~r1_tarski('#skF_5', C_139) | ~m1_subset_1(C_139, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_59, c_1121])).
% 6.09/2.21  tff(c_1182, plain, (r1_tarski('#skF_5', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_30, c_1162])).
% 6.09/2.21  tff(c_1198, plain, (r1_tarski('#skF_5', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1182])).
% 6.09/2.21  tff(c_1200, plain, $false, inference(negUnitSimplification, [status(thm)], [c_360, c_1198])).
% 6.09/2.21  tff(c_1218, plain, (![D_141]: (~r2_hidden('#skF_3', D_141) | ~r1_tarski(D_141, '#skF_4') | ~v3_pre_topc(D_141, '#skF_2') | ~m1_subset_1(D_141, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_36])).
% 6.09/2.21  tff(c_1229, plain, (~r2_hidden('#skF_3', '#skF_5') | ~r1_tarski('#skF_5', '#skF_4') | ~v3_pre_topc('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_59, c_1218])).
% 6.09/2.21  tff(c_1240, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_55, c_56, c_58, c_1229])).
% 6.09/2.21  tff(c_1241, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_54])).
% 6.09/2.21  tff(c_18, plain, (![A_16, B_17]: (m1_subset_1(k1_tops_1(A_16, B_17), k1_zfmisc_1(u1_struct_0(A_16))) | ~m1_subset_1(B_17, k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.09/2.21  tff(c_1242, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_54])).
% 6.09/2.21  tff(c_52, plain, (![D_41]: (~r2_hidden('#skF_3', D_41) | ~r1_tarski(D_41, '#skF_4') | ~v3_pre_topc(D_41, '#skF_2') | ~m1_subset_1(D_41, k1_zfmisc_1(u1_struct_0('#skF_2'))) | m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.09/2.21  tff(c_1468, plain, (![D_183]: (~r2_hidden('#skF_3', D_183) | ~r1_tarski(D_183, '#skF_4') | ~v3_pre_topc(D_183, '#skF_2') | ~m1_subset_1(D_183, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_1242, c_52])).
% 6.09/2.21  tff(c_1472, plain, (![B_17]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', B_17)) | ~r1_tarski(k1_tops_1('#skF_2', B_17), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', B_17), '#skF_2') | ~m1_subset_1(B_17, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_18, c_1468])).
% 6.09/2.21  tff(c_1733, plain, (![B_206]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', B_206)) | ~r1_tarski(k1_tops_1('#skF_2', B_206), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', B_206), '#skF_2') | ~m1_subset_1(B_206, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1472])).
% 6.09/2.21  tff(c_1747, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_30, c_1733])).
% 6.09/2.21  tff(c_1758, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1368, c_1331, c_1241, c_1747])).
% 6.09/2.21  tff(c_1759, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_42])).
% 6.09/2.21  tff(c_1832, plain, (![A_224, B_225]: (m1_subset_1(k1_tops_1(A_224, B_225), k1_zfmisc_1(u1_struct_0(A_224))) | ~m1_subset_1(B_225, k1_zfmisc_1(u1_struct_0(A_224))) | ~l1_pre_topc(A_224))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.09/2.21  tff(c_1760, plain, (~r2_hidden('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_42])).
% 6.09/2.21  tff(c_40, plain, (![D_41]: (~r2_hidden('#skF_3', D_41) | ~r1_tarski(D_41, '#skF_4') | ~v3_pre_topc(D_41, '#skF_2') | ~m1_subset_1(D_41, k1_zfmisc_1(u1_struct_0('#skF_2'))) | r2_hidden('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.09/2.21  tff(c_1791, plain, (![D_41]: (~r2_hidden('#skF_3', D_41) | ~r1_tarski(D_41, '#skF_4') | ~v3_pre_topc(D_41, '#skF_2') | ~m1_subset_1(D_41, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_1760, c_40])).
% 6.09/2.21  tff(c_1838, plain, (![B_225]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', B_225)) | ~r1_tarski(k1_tops_1('#skF_2', B_225), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', B_225), '#skF_2') | ~m1_subset_1(B_225, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_1832, c_1791])).
% 6.09/2.21  tff(c_2331, plain, (![B_278]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', B_278)) | ~r1_tarski(k1_tops_1('#skF_2', B_278), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', B_278), '#skF_2') | ~m1_subset_1(B_278, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1838])).
% 6.09/2.21  tff(c_2345, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_30, c_2331])).
% 6.09/2.21  tff(c_2356, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1903, c_1831, c_1759, c_2345])).
% 6.09/2.21  tff(c_2357, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_46])).
% 6.09/2.21  tff(c_2358, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_46])).
% 6.09/2.21  tff(c_44, plain, (![D_41]: (~r2_hidden('#skF_3', D_41) | ~r1_tarski(D_41, '#skF_4') | ~v3_pre_topc(D_41, '#skF_2') | ~m1_subset_1(D_41, k1_zfmisc_1(u1_struct_0('#skF_2'))) | r1_tarski('#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.09/2.21  tff(c_3038, plain, (![D_357]: (~r2_hidden('#skF_3', D_357) | ~r1_tarski(D_357, '#skF_4') | ~v3_pre_topc(D_357, '#skF_2') | ~m1_subset_1(D_357, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_2358, c_44])).
% 6.09/2.21  tff(c_3042, plain, (![B_17]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', B_17)) | ~r1_tarski(k1_tops_1('#skF_2', B_17), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', B_17), '#skF_2') | ~m1_subset_1(B_17, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_18, c_3038])).
% 6.09/2.21  tff(c_3350, plain, (![B_380]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', B_380)) | ~r1_tarski(k1_tops_1('#skF_2', B_380), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', B_380), '#skF_2') | ~m1_subset_1(B_380, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_3042])).
% 6.09/2.21  tff(c_3364, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_30, c_3350])).
% 6.09/2.21  tff(c_3375, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2431, c_2417, c_2357, c_3364])).
% 6.09/2.21  tff(c_3376, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_50])).
% 6.09/2.21  tff(c_3377, plain, (~v3_pre_topc('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_50])).
% 6.09/2.21  tff(c_48, plain, (![D_41]: (~r2_hidden('#skF_3', D_41) | ~r1_tarski(D_41, '#skF_4') | ~v3_pre_topc(D_41, '#skF_2') | ~m1_subset_1(D_41, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v3_pre_topc('#skF_5', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.09/2.21  tff(c_4679, plain, (![D_516]: (~r2_hidden('#skF_3', D_516) | ~r1_tarski(D_516, '#skF_4') | ~v3_pre_topc(D_516, '#skF_2') | ~m1_subset_1(D_516, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_3377, c_48])).
% 6.09/2.21  tff(c_4683, plain, (![B_17]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', B_17)) | ~r1_tarski(k1_tops_1('#skF_2', B_17), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', B_17), '#skF_2') | ~m1_subset_1(B_17, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_18, c_4679])).
% 6.09/2.21  tff(c_5056, plain, (![B_550]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', B_550)) | ~r1_tarski(k1_tops_1('#skF_2', B_550), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', B_550), '#skF_2') | ~m1_subset_1(B_550, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_4683])).
% 6.09/2.21  tff(c_5070, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_30, c_5056])).
% 6.09/2.21  tff(c_5081, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4144, c_3437, c_3376, c_5070])).
% 6.09/2.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.09/2.21  
% 6.09/2.21  Inference rules
% 6.09/2.21  ----------------------
% 6.09/2.21  #Ref     : 0
% 6.09/2.21  #Sup     : 1051
% 6.09/2.21  #Fact    : 0
% 6.09/2.21  #Define  : 0
% 6.09/2.21  #Split   : 64
% 6.09/2.21  #Chain   : 0
% 6.09/2.21  #Close   : 0
% 6.09/2.21  
% 6.09/2.21  Ordering : KBO
% 6.09/2.21  
% 6.09/2.21  Simplification rules
% 6.09/2.21  ----------------------
% 6.09/2.21  #Subsume      : 135
% 6.09/2.21  #Demod        : 738
% 6.09/2.21  #Tautology    : 269
% 6.09/2.21  #SimpNegUnit  : 43
% 6.09/2.21  #BackRed      : 10
% 6.09/2.21  
% 6.09/2.21  #Partial instantiations: 0
% 6.09/2.21  #Strategies tried      : 1
% 6.09/2.21  
% 6.09/2.21  Timing (in seconds)
% 6.09/2.21  ----------------------
% 6.09/2.21  Preprocessing        : 0.32
% 6.09/2.21  Parsing              : 0.18
% 6.09/2.21  CNF conversion       : 0.02
% 6.09/2.21  Main loop            : 1.11
% 6.09/2.21  Inferencing          : 0.39
% 6.09/2.21  Reduction            : 0.35
% 6.09/2.21  Demodulation         : 0.24
% 6.09/2.21  BG Simplification    : 0.04
% 6.09/2.21  Subsumption          : 0.24
% 6.09/2.21  Abstraction          : 0.05
% 6.09/2.21  MUC search           : 0.00
% 6.09/2.21  Cooper               : 0.00
% 6.09/2.21  Total                : 1.47
% 6.09/2.21  Index Insertion      : 0.00
% 6.09/2.21  Index Deletion       : 0.00
% 6.09/2.21  Index Matching       : 0.00
% 6.09/2.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
