%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:03 EST 2020

% Result     : Theorem 7.68s
% Output     : CNFRefutation 7.68s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 744 expanded)
%              Number of leaves         :   49 ( 269 expanded)
%              Depth                    :   18
%              Number of atoms          :  268 (1567 expanded)
%              Number of equality atoms :   60 ( 352 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tops_1 > v2_tops_1 > v1_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k2_enumset1 > k9_subset_1 > k1_enumset1 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v3_tops_1,type,(
    v3_tops_1: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_159,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => ( v3_tops_1(B,A)
              <=> B = k2_tops_1(A,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_tops_1)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_127,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> r1_tarski(B,k2_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tops_1)).

tff(f_147,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v2_tops_1(B,A)
              & v4_pre_topc(B,A) )
           => v3_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_tops_1)).

tff(f_48,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_50,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_102,axiom,(
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

tff(f_136,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_tops_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_118,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_109,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_1)).

tff(c_64,plain,
    ( k2_tops_1('#skF_2','#skF_3') != '#skF_3'
    | ~ v3_tops_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_95,plain,(
    ~ v3_tops_1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_62,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_38,plain,(
    ! [A_33] :
      ( l1_struct_0(A_33)
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_85,plain,(
    ! [A_57] :
      ( u1_struct_0(A_57) = k2_struct_0(A_57)
      | ~ l1_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_90,plain,(
    ! [A_58] :
      ( u1_struct_0(A_58) = k2_struct_0(A_58)
      | ~ l1_pre_topc(A_58) ) ),
    inference(resolution,[status(thm)],[c_38,c_85])).

tff(c_94,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_90])).

tff(c_60,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_96,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_60])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_70,plain,
    ( v3_tops_1('#skF_3','#skF_2')
    | k2_tops_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_133,plain,(
    k2_tops_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_70])).

tff(c_562,plain,(
    ! [B_132,A_133] :
      ( v2_tops_1(B_132,A_133)
      | ~ r1_tarski(B_132,k2_tops_1(A_133,B_132))
      | ~ m1_subset_1(B_132,k1_zfmisc_1(u1_struct_0(A_133)))
      | ~ l1_pre_topc(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_567,plain,
    ( v2_tops_1('#skF_3','#skF_2')
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_562])).

tff(c_570,plain,(
    v2_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_96,c_94,c_12,c_567])).

tff(c_58,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_1001,plain,(
    ! [B_176,A_177] :
      ( v3_tops_1(B_176,A_177)
      | ~ v4_pre_topc(B_176,A_177)
      | ~ v2_tops_1(B_176,A_177)
      | ~ m1_subset_1(B_176,k1_zfmisc_1(u1_struct_0(A_177)))
      | ~ l1_pre_topc(A_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_1016,plain,(
    ! [B_176] :
      ( v3_tops_1(B_176,'#skF_2')
      | ~ v4_pre_topc(B_176,'#skF_2')
      | ~ v2_tops_1(B_176,'#skF_2')
      | ~ m1_subset_1(B_176,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_1001])).

tff(c_1432,plain,(
    ! [B_200] :
      ( v3_tops_1(B_200,'#skF_2')
      | ~ v4_pre_topc(B_200,'#skF_2')
      | ~ v2_tops_1(B_200,'#skF_2')
      | ~ m1_subset_1(B_200,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1016])).

tff(c_1451,plain,
    ( v3_tops_1('#skF_3','#skF_2')
    | ~ v4_pre_topc('#skF_3','#skF_2')
    | ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_96,c_1432])).

tff(c_1465,plain,(
    v3_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_570,c_58,c_1451])).

tff(c_1467,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_1465])).

tff(c_1468,plain,(
    k2_tops_1('#skF_2','#skF_3') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_20,plain,(
    ! [A_15] : k2_subset_1(A_15) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_22,plain,(
    ! [A_16] : m1_subset_1(k2_subset_1(A_16),k1_zfmisc_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_71,plain,(
    ! [A_16] : m1_subset_1(A_16,k1_zfmisc_1(A_16)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22])).

tff(c_1470,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_60])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1530,plain,(
    ! [C_216,B_217,A_218] :
      ( ~ v1_xboole_0(C_216)
      | ~ m1_subset_1(B_217,k1_zfmisc_1(C_216))
      | ~ r2_hidden(A_218,B_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1535,plain,(
    ! [A_218] :
      ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ r2_hidden(A_218,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1470,c_1530])).

tff(c_1561,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1535])).

tff(c_1583,plain,(
    ! [A_235,C_236,B_237] :
      ( m1_subset_1(A_235,C_236)
      | ~ m1_subset_1(B_237,k1_zfmisc_1(C_236))
      | ~ r2_hidden(A_235,B_237) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1588,plain,(
    ! [A_235] :
      ( m1_subset_1(A_235,k2_struct_0('#skF_2'))
      | ~ r2_hidden(A_235,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1470,c_1583])).

tff(c_30,plain,(
    ! [A_24,B_25] :
      ( r2_hidden(A_24,B_25)
      | v1_xboole_0(B_25)
      | ~ m1_subset_1(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1518,plain,(
    ! [A_214,B_215] :
      ( ~ r2_hidden('#skF_1'(A_214,B_215),B_215)
      | r1_tarski(A_214,B_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1616,plain,(
    ! [A_245,B_246] :
      ( r1_tarski(A_245,B_246)
      | v1_xboole_0(B_246)
      | ~ m1_subset_1('#skF_1'(A_245,B_246),B_246) ) ),
    inference(resolution,[status(thm)],[c_30,c_1518])).

tff(c_1624,plain,(
    ! [A_245] :
      ( r1_tarski(A_245,k2_struct_0('#skF_2'))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ r2_hidden('#skF_1'(A_245,k2_struct_0('#skF_2')),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1588,c_1616])).

tff(c_1630,plain,(
    ! [A_247] :
      ( r1_tarski(A_247,k2_struct_0('#skF_2'))
      | ~ r2_hidden('#skF_1'(A_247,k2_struct_0('#skF_2')),'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1561,c_1624])).

tff(c_1639,plain,(
    r1_tarski('#skF_3',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_6,c_1630])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( k3_xboole_0(A_8,B_9) = A_8
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1650,plain,(
    k3_xboole_0('#skF_3',k2_struct_0('#skF_2')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1639,c_14])).

tff(c_1660,plain,(
    ! [A_248,B_249,C_250] :
      ( k9_subset_1(A_248,B_249,C_250) = k3_xboole_0(B_249,C_250)
      | ~ m1_subset_1(C_250,k1_zfmisc_1(A_248)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1673,plain,(
    ! [A_16,B_249] : k9_subset_1(A_16,B_249,A_16) = k3_xboole_0(B_249,A_16) ),
    inference(resolution,[status(thm)],[c_71,c_1660])).

tff(c_1674,plain,(
    ! [A_251,B_252] :
      ( k2_pre_topc(A_251,B_252) = B_252
      | ~ v4_pre_topc(B_252,A_251)
      | ~ m1_subset_1(B_252,k1_zfmisc_1(u1_struct_0(A_251)))
      | ~ l1_pre_topc(A_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1685,plain,(
    ! [B_252] :
      ( k2_pre_topc('#skF_2',B_252) = B_252
      | ~ v4_pre_topc(B_252,'#skF_2')
      | ~ m1_subset_1(B_252,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_1674])).

tff(c_1735,plain,(
    ! [B_259] :
      ( k2_pre_topc('#skF_2',B_259) = B_259
      | ~ v4_pre_topc(B_259,'#skF_2')
      | ~ m1_subset_1(B_259,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1685])).

tff(c_1746,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_1470,c_1735])).

tff(c_1755,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1746])).

tff(c_1469,plain,(
    v3_tops_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_6978,plain,(
    ! [A_611,B_612] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_611),B_612),A_611)
      | ~ v3_tops_1(B_612,A_611)
      | ~ m1_subset_1(B_612,k1_zfmisc_1(u1_struct_0(A_611)))
      | ~ l1_pre_topc(A_611) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_6981,plain,(
    ! [B_612] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_2'),B_612),'#skF_2')
      | ~ v3_tops_1(B_612,'#skF_2')
      | ~ m1_subset_1(B_612,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_6978])).

tff(c_6983,plain,(
    ! [B_612] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_2'),B_612),'#skF_2')
      | ~ v3_tops_1(B_612,'#skF_2')
      | ~ m1_subset_1(B_612,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_94,c_6981])).

tff(c_24,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(k3_subset_1(A_17,B_18),k1_zfmisc_1(A_17))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6566,plain,(
    ! [A_564,B_565] :
      ( k2_pre_topc(A_564,B_565) = k2_struct_0(A_564)
      | ~ v1_tops_1(B_565,A_564)
      | ~ m1_subset_1(B_565,k1_zfmisc_1(u1_struct_0(A_564)))
      | ~ l1_pre_topc(A_564) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_7385,plain,(
    ! [A_665,B_666] :
      ( k2_pre_topc(A_665,k3_subset_1(u1_struct_0(A_665),B_666)) = k2_struct_0(A_665)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(A_665),B_666),A_665)
      | ~ l1_pre_topc(A_665)
      | ~ m1_subset_1(B_666,k1_zfmisc_1(u1_struct_0(A_665))) ) ),
    inference(resolution,[status(thm)],[c_24,c_6566])).

tff(c_7394,plain,(
    ! [B_666] :
      ( k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),B_666)) = k2_struct_0('#skF_2')
      | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_2'),B_666),'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ m1_subset_1(B_666,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_7385])).

tff(c_8238,plain,(
    ! [B_710] :
      ( k2_pre_topc('#skF_2',k3_subset_1(k2_struct_0('#skF_2'),B_710)) = k2_struct_0('#skF_2')
      | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_2'),B_710),'#skF_2')
      | ~ m1_subset_1(B_710,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_62,c_94,c_7394])).

tff(c_8720,plain,(
    ! [B_734] :
      ( k2_pre_topc('#skF_2',k3_subset_1(k2_struct_0('#skF_2'),B_734)) = k2_struct_0('#skF_2')
      | ~ v3_tops_1(B_734,'#skF_2')
      | ~ m1_subset_1(B_734,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_6983,c_8238])).

tff(c_8739,plain,
    ( k2_pre_topc('#skF_2',k3_subset_1(k2_struct_0('#skF_2'),'#skF_3')) = k2_struct_0('#skF_2')
    | ~ v3_tops_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_1470,c_8720])).

tff(c_8750,plain,(
    k2_pre_topc('#skF_2',k3_subset_1(k2_struct_0('#skF_2'),'#skF_3')) = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1469,c_8739])).

tff(c_7072,plain,(
    ! [A_627,B_628] :
      ( k9_subset_1(u1_struct_0(A_627),k2_pre_topc(A_627,B_628),k2_pre_topc(A_627,k3_subset_1(u1_struct_0(A_627),B_628))) = k2_tops_1(A_627,B_628)
      | ~ m1_subset_1(B_628,k1_zfmisc_1(u1_struct_0(A_627)))
      | ~ l1_pre_topc(A_627) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_7087,plain,(
    ! [B_628] :
      ( k9_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2',B_628),k2_pre_topc('#skF_2',k3_subset_1(k2_struct_0('#skF_2'),B_628))) = k2_tops_1('#skF_2',B_628)
      | ~ m1_subset_1(B_628,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_7072])).

tff(c_7095,plain,(
    ! [B_628] :
      ( k9_subset_1(k2_struct_0('#skF_2'),k2_pre_topc('#skF_2',B_628),k2_pre_topc('#skF_2',k3_subset_1(k2_struct_0('#skF_2'),B_628))) = k2_tops_1('#skF_2',B_628)
      | ~ m1_subset_1(B_628,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_94,c_94,c_7087])).

tff(c_8759,plain,
    ( k9_subset_1(k2_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),k2_struct_0('#skF_2')) = k2_tops_1('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_8750,c_7095])).

tff(c_8766,plain,(
    k2_tops_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1470,c_1650,c_1673,c_1755,c_8759])).

tff(c_8768,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1468,c_8766])).

tff(c_8770,plain,(
    v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1535])).

tff(c_1537,plain,(
    ! [A_219,A_220] :
      ( ~ v1_xboole_0(A_219)
      | ~ r2_hidden(A_220,A_219) ) ),
    inference(resolution,[status(thm)],[c_71,c_1530])).

tff(c_1545,plain,(
    ! [A_1,B_2] :
      ( ~ v1_xboole_0(A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_1537])).

tff(c_8771,plain,(
    ! [A_735] : ~ r2_hidden(A_735,'#skF_3') ),
    inference(splitRight,[status(thm)],[c_1535])).

tff(c_8782,plain,(
    ! [B_736] : r1_tarski('#skF_3',B_736) ),
    inference(resolution,[status(thm)],[c_6,c_8771])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8818,plain,(
    ! [B_742] :
      ( B_742 = '#skF_3'
      | ~ r1_tarski(B_742,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_8782,c_8])).

tff(c_8836,plain,(
    ! [A_743] :
      ( A_743 = '#skF_3'
      | ~ v1_xboole_0(A_743) ) ),
    inference(resolution,[status(thm)],[c_1545,c_8818])).

tff(c_8840,plain,(
    k2_struct_0('#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_8770,c_8836])).

tff(c_8843,plain,(
    u1_struct_0('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8840,c_94])).

tff(c_1495,plain,(
    ! [A_205,B_206] :
      ( k3_xboole_0(A_205,B_206) = A_205
      | ~ r1_tarski(A_205,B_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1499,plain,(
    ! [B_7] : k3_xboole_0(B_7,B_7) = B_7 ),
    inference(resolution,[status(thm)],[c_12,c_1495])).

tff(c_8892,plain,(
    ! [A_755,B_756,C_757] :
      ( k9_subset_1(A_755,B_756,C_757) = k3_xboole_0(B_756,C_757)
      | ~ m1_subset_1(C_757,k1_zfmisc_1(A_755)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_8898,plain,(
    ! [A_16,B_756] : k9_subset_1(A_16,B_756,A_16) = k3_xboole_0(B_756,A_16) ),
    inference(resolution,[status(thm)],[c_71,c_8892])).

tff(c_8965,plain,(
    ! [A_769,B_770] :
      ( k2_pre_topc(A_769,B_770) = B_770
      | ~ v4_pre_topc(B_770,A_769)
      | ~ m1_subset_1(B_770,k1_zfmisc_1(u1_struct_0(A_769)))
      | ~ l1_pre_topc(A_769) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_8976,plain,(
    ! [B_770] :
      ( k2_pre_topc('#skF_2',B_770) = B_770
      | ~ v4_pre_topc(B_770,'#skF_2')
      | ~ m1_subset_1(B_770,k1_zfmisc_1('#skF_3'))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8843,c_8965])).

tff(c_9023,plain,(
    ! [B_779] :
      ( k2_pre_topc('#skF_2',B_779) = B_779
      | ~ v4_pre_topc(B_779,'#skF_2')
      | ~ m1_subset_1(B_779,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_8976])).

tff(c_9035,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_71,c_9023])).

tff(c_9040,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_9035])).

tff(c_8841,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8840,c_8770])).

tff(c_8863,plain,(
    ! [A_746,B_747] :
      ( m1_subset_1(k3_subset_1(A_746,B_747),k1_zfmisc_1(A_746))
      | ~ m1_subset_1(B_747,k1_zfmisc_1(A_746)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_34,plain,(
    ! [C_31,B_30,A_29] :
      ( ~ v1_xboole_0(C_31)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(C_31))
      | ~ r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_9045,plain,(
    ! [A_780,A_781,B_782] :
      ( ~ v1_xboole_0(A_780)
      | ~ r2_hidden(A_781,k3_subset_1(A_780,B_782))
      | ~ m1_subset_1(B_782,k1_zfmisc_1(A_780)) ) ),
    inference(resolution,[status(thm)],[c_8863,c_34])).

tff(c_9094,plain,(
    ! [A_786,B_787,B_788] :
      ( ~ v1_xboole_0(A_786)
      | ~ m1_subset_1(B_787,k1_zfmisc_1(A_786))
      | r1_tarski(k3_subset_1(A_786,B_787),B_788) ) ),
    inference(resolution,[status(thm)],[c_6,c_9045])).

tff(c_8788,plain,(
    ! [B_736] :
      ( B_736 = '#skF_3'
      | ~ r1_tarski(B_736,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_8782,c_8])).

tff(c_9121,plain,(
    ! [A_789,B_790] :
      ( k3_subset_1(A_789,B_790) = '#skF_3'
      | ~ v1_xboole_0(A_789)
      | ~ m1_subset_1(B_790,k1_zfmisc_1(A_789)) ) ),
    inference(resolution,[status(thm)],[c_9094,c_8788])).

tff(c_9161,plain,(
    ! [A_793] :
      ( k3_subset_1(A_793,A_793) = '#skF_3'
      | ~ v1_xboole_0(A_793) ) ),
    inference(resolution,[status(thm)],[c_71,c_9121])).

tff(c_9164,plain,(
    k3_subset_1('#skF_3','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_8841,c_9161])).

tff(c_10582,plain,(
    ! [A_899,B_900] :
      ( k9_subset_1(u1_struct_0(A_899),k2_pre_topc(A_899,B_900),k2_pre_topc(A_899,k3_subset_1(u1_struct_0(A_899),B_900))) = k2_tops_1(A_899,B_900)
      | ~ m1_subset_1(B_900,k1_zfmisc_1(u1_struct_0(A_899)))
      | ~ l1_pre_topc(A_899) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_10603,plain,
    ( k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'))) = k2_tops_1('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_9040,c_10582])).

tff(c_10613,plain,(
    k2_tops_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_71,c_8843,c_1499,c_8898,c_9040,c_9164,c_8843,c_8843,c_10603])).

tff(c_10615,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1468,c_10613])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:43:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.68/2.81  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.68/2.82  
% 7.68/2.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.68/2.82  %$ v4_pre_topc > v3_tops_1 > v2_tops_1 > v1_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k2_enumset1 > k9_subset_1 > k1_enumset1 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 7.68/2.82  
% 7.68/2.82  %Foreground sorts:
% 7.68/2.82  
% 7.68/2.82  
% 7.68/2.82  %Background operators:
% 7.68/2.82  
% 7.68/2.82  
% 7.68/2.82  %Foreground operators:
% 7.68/2.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.68/2.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.68/2.82  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 7.68/2.82  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 7.68/2.82  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.68/2.82  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 7.68/2.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.68/2.82  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.68/2.82  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.68/2.82  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 7.68/2.82  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 7.68/2.82  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.68/2.82  tff('#skF_2', type, '#skF_2': $i).
% 7.68/2.82  tff('#skF_3', type, '#skF_3': $i).
% 7.68/2.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.68/2.82  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.68/2.82  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 7.68/2.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.68/2.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.68/2.82  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.68/2.82  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.68/2.82  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.68/2.82  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.68/2.82  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 7.68/2.82  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 7.68/2.82  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.68/2.82  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 7.68/2.82  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 7.68/2.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.68/2.82  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.68/2.82  
% 7.68/2.84  tff(f_159, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => (v3_tops_1(B, A) <=> (B = k2_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_tops_1)).
% 7.68/2.84  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 7.68/2.84  tff(f_83, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 7.68/2.84  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.68/2.84  tff(f_127, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tops_1)).
% 7.68/2.84  tff(f_147, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tops_1(B, A) & v4_pre_topc(B, A)) => v3_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t93_tops_1)).
% 7.68/2.84  tff(f_48, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 7.68/2.84  tff(f_50, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 7.68/2.84  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 7.68/2.84  tff(f_79, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 7.68/2.84  tff(f_72, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 7.68/2.84  tff(f_66, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 7.68/2.84  tff(f_42, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.68/2.84  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 7.68/2.84  tff(f_102, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 7.68/2.84  tff(f_136, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_tops_1)).
% 7.68/2.84  tff(f_54, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 7.68/2.84  tff(f_118, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_1)).
% 7.68/2.84  tff(f_109, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_1)).
% 7.68/2.84  tff(c_64, plain, (k2_tops_1('#skF_2', '#skF_3')!='#skF_3' | ~v3_tops_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 7.68/2.84  tff(c_95, plain, (~v3_tops_1('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_64])).
% 7.68/2.84  tff(c_62, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 7.68/2.84  tff(c_38, plain, (![A_33]: (l1_struct_0(A_33) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.68/2.84  tff(c_85, plain, (![A_57]: (u1_struct_0(A_57)=k2_struct_0(A_57) | ~l1_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.68/2.84  tff(c_90, plain, (![A_58]: (u1_struct_0(A_58)=k2_struct_0(A_58) | ~l1_pre_topc(A_58))), inference(resolution, [status(thm)], [c_38, c_85])).
% 7.68/2.84  tff(c_94, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_62, c_90])).
% 7.68/2.84  tff(c_60, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_159])).
% 7.68/2.84  tff(c_96, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_60])).
% 7.68/2.84  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.68/2.84  tff(c_70, plain, (v3_tops_1('#skF_3', '#skF_2') | k2_tops_1('#skF_2', '#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_159])).
% 7.68/2.84  tff(c_133, plain, (k2_tops_1('#skF_2', '#skF_3')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_95, c_70])).
% 7.68/2.84  tff(c_562, plain, (![B_132, A_133]: (v2_tops_1(B_132, A_133) | ~r1_tarski(B_132, k2_tops_1(A_133, B_132)) | ~m1_subset_1(B_132, k1_zfmisc_1(u1_struct_0(A_133))) | ~l1_pre_topc(A_133))), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.68/2.84  tff(c_567, plain, (v2_tops_1('#skF_3', '#skF_2') | ~r1_tarski('#skF_3', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_133, c_562])).
% 7.68/2.84  tff(c_570, plain, (v2_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_96, c_94, c_12, c_567])).
% 7.68/2.84  tff(c_58, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 7.68/2.84  tff(c_1001, plain, (![B_176, A_177]: (v3_tops_1(B_176, A_177) | ~v4_pre_topc(B_176, A_177) | ~v2_tops_1(B_176, A_177) | ~m1_subset_1(B_176, k1_zfmisc_1(u1_struct_0(A_177))) | ~l1_pre_topc(A_177))), inference(cnfTransformation, [status(thm)], [f_147])).
% 7.68/2.84  tff(c_1016, plain, (![B_176]: (v3_tops_1(B_176, '#skF_2') | ~v4_pre_topc(B_176, '#skF_2') | ~v2_tops_1(B_176, '#skF_2') | ~m1_subset_1(B_176, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_94, c_1001])).
% 7.68/2.84  tff(c_1432, plain, (![B_200]: (v3_tops_1(B_200, '#skF_2') | ~v4_pre_topc(B_200, '#skF_2') | ~v2_tops_1(B_200, '#skF_2') | ~m1_subset_1(B_200, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1016])).
% 7.68/2.84  tff(c_1451, plain, (v3_tops_1('#skF_3', '#skF_2') | ~v4_pre_topc('#skF_3', '#skF_2') | ~v2_tops_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_96, c_1432])).
% 7.68/2.84  tff(c_1465, plain, (v3_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_570, c_58, c_1451])).
% 7.68/2.84  tff(c_1467, plain, $false, inference(negUnitSimplification, [status(thm)], [c_95, c_1465])).
% 7.68/2.84  tff(c_1468, plain, (k2_tops_1('#skF_2', '#skF_3')!='#skF_3'), inference(splitRight, [status(thm)], [c_64])).
% 7.68/2.84  tff(c_20, plain, (![A_15]: (k2_subset_1(A_15)=A_15)), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.68/2.84  tff(c_22, plain, (![A_16]: (m1_subset_1(k2_subset_1(A_16), k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.68/2.84  tff(c_71, plain, (![A_16]: (m1_subset_1(A_16, k1_zfmisc_1(A_16)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22])).
% 7.68/2.84  tff(c_1470, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_60])).
% 7.68/2.84  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.68/2.84  tff(c_1530, plain, (![C_216, B_217, A_218]: (~v1_xboole_0(C_216) | ~m1_subset_1(B_217, k1_zfmisc_1(C_216)) | ~r2_hidden(A_218, B_217))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.68/2.84  tff(c_1535, plain, (![A_218]: (~v1_xboole_0(k2_struct_0('#skF_2')) | ~r2_hidden(A_218, '#skF_3'))), inference(resolution, [status(thm)], [c_1470, c_1530])).
% 7.68/2.84  tff(c_1561, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1535])).
% 7.68/2.84  tff(c_1583, plain, (![A_235, C_236, B_237]: (m1_subset_1(A_235, C_236) | ~m1_subset_1(B_237, k1_zfmisc_1(C_236)) | ~r2_hidden(A_235, B_237))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.68/2.84  tff(c_1588, plain, (![A_235]: (m1_subset_1(A_235, k2_struct_0('#skF_2')) | ~r2_hidden(A_235, '#skF_3'))), inference(resolution, [status(thm)], [c_1470, c_1583])).
% 7.68/2.84  tff(c_30, plain, (![A_24, B_25]: (r2_hidden(A_24, B_25) | v1_xboole_0(B_25) | ~m1_subset_1(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.68/2.84  tff(c_1518, plain, (![A_214, B_215]: (~r2_hidden('#skF_1'(A_214, B_215), B_215) | r1_tarski(A_214, B_215))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.68/2.84  tff(c_1616, plain, (![A_245, B_246]: (r1_tarski(A_245, B_246) | v1_xboole_0(B_246) | ~m1_subset_1('#skF_1'(A_245, B_246), B_246))), inference(resolution, [status(thm)], [c_30, c_1518])).
% 7.68/2.84  tff(c_1624, plain, (![A_245]: (r1_tarski(A_245, k2_struct_0('#skF_2')) | v1_xboole_0(k2_struct_0('#skF_2')) | ~r2_hidden('#skF_1'(A_245, k2_struct_0('#skF_2')), '#skF_3'))), inference(resolution, [status(thm)], [c_1588, c_1616])).
% 7.68/2.84  tff(c_1630, plain, (![A_247]: (r1_tarski(A_247, k2_struct_0('#skF_2')) | ~r2_hidden('#skF_1'(A_247, k2_struct_0('#skF_2')), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_1561, c_1624])).
% 7.68/2.84  tff(c_1639, plain, (r1_tarski('#skF_3', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_6, c_1630])).
% 7.68/2.84  tff(c_14, plain, (![A_8, B_9]: (k3_xboole_0(A_8, B_9)=A_8 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.68/2.84  tff(c_1650, plain, (k3_xboole_0('#skF_3', k2_struct_0('#skF_2'))='#skF_3'), inference(resolution, [status(thm)], [c_1639, c_14])).
% 7.68/2.84  tff(c_1660, plain, (![A_248, B_249, C_250]: (k9_subset_1(A_248, B_249, C_250)=k3_xboole_0(B_249, C_250) | ~m1_subset_1(C_250, k1_zfmisc_1(A_248)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.68/2.84  tff(c_1673, plain, (![A_16, B_249]: (k9_subset_1(A_16, B_249, A_16)=k3_xboole_0(B_249, A_16))), inference(resolution, [status(thm)], [c_71, c_1660])).
% 7.68/2.84  tff(c_1674, plain, (![A_251, B_252]: (k2_pre_topc(A_251, B_252)=B_252 | ~v4_pre_topc(B_252, A_251) | ~m1_subset_1(B_252, k1_zfmisc_1(u1_struct_0(A_251))) | ~l1_pre_topc(A_251))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.68/2.84  tff(c_1685, plain, (![B_252]: (k2_pre_topc('#skF_2', B_252)=B_252 | ~v4_pre_topc(B_252, '#skF_2') | ~m1_subset_1(B_252, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_94, c_1674])).
% 7.68/2.84  tff(c_1735, plain, (![B_259]: (k2_pre_topc('#skF_2', B_259)=B_259 | ~v4_pre_topc(B_259, '#skF_2') | ~m1_subset_1(B_259, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1685])).
% 7.68/2.84  tff(c_1746, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_1470, c_1735])).
% 7.68/2.84  tff(c_1755, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1746])).
% 7.68/2.84  tff(c_1469, plain, (v3_tops_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_64])).
% 7.68/2.84  tff(c_6978, plain, (![A_611, B_612]: (v1_tops_1(k3_subset_1(u1_struct_0(A_611), B_612), A_611) | ~v3_tops_1(B_612, A_611) | ~m1_subset_1(B_612, k1_zfmisc_1(u1_struct_0(A_611))) | ~l1_pre_topc(A_611))), inference(cnfTransformation, [status(thm)], [f_136])).
% 7.68/2.84  tff(c_6981, plain, (![B_612]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_2'), B_612), '#skF_2') | ~v3_tops_1(B_612, '#skF_2') | ~m1_subset_1(B_612, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_94, c_6978])).
% 7.68/2.84  tff(c_6983, plain, (![B_612]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_2'), B_612), '#skF_2') | ~v3_tops_1(B_612, '#skF_2') | ~m1_subset_1(B_612, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_94, c_6981])).
% 7.68/2.84  tff(c_24, plain, (![A_17, B_18]: (m1_subset_1(k3_subset_1(A_17, B_18), k1_zfmisc_1(A_17)) | ~m1_subset_1(B_18, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.68/2.84  tff(c_6566, plain, (![A_564, B_565]: (k2_pre_topc(A_564, B_565)=k2_struct_0(A_564) | ~v1_tops_1(B_565, A_564) | ~m1_subset_1(B_565, k1_zfmisc_1(u1_struct_0(A_564))) | ~l1_pre_topc(A_564))), inference(cnfTransformation, [status(thm)], [f_118])).
% 7.68/2.84  tff(c_7385, plain, (![A_665, B_666]: (k2_pre_topc(A_665, k3_subset_1(u1_struct_0(A_665), B_666))=k2_struct_0(A_665) | ~v1_tops_1(k3_subset_1(u1_struct_0(A_665), B_666), A_665) | ~l1_pre_topc(A_665) | ~m1_subset_1(B_666, k1_zfmisc_1(u1_struct_0(A_665))))), inference(resolution, [status(thm)], [c_24, c_6566])).
% 7.68/2.84  tff(c_7394, plain, (![B_666]: (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), B_666))=k2_struct_0('#skF_2') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_2'), B_666), '#skF_2') | ~l1_pre_topc('#skF_2') | ~m1_subset_1(B_666, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_94, c_7385])).
% 7.68/2.84  tff(c_8238, plain, (![B_710]: (k2_pre_topc('#skF_2', k3_subset_1(k2_struct_0('#skF_2'), B_710))=k2_struct_0('#skF_2') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_2'), B_710), '#skF_2') | ~m1_subset_1(B_710, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_62, c_94, c_7394])).
% 7.68/2.84  tff(c_8720, plain, (![B_734]: (k2_pre_topc('#skF_2', k3_subset_1(k2_struct_0('#skF_2'), B_734))=k2_struct_0('#skF_2') | ~v3_tops_1(B_734, '#skF_2') | ~m1_subset_1(B_734, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_6983, c_8238])).
% 7.68/2.84  tff(c_8739, plain, (k2_pre_topc('#skF_2', k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'))=k2_struct_0('#skF_2') | ~v3_tops_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_1470, c_8720])).
% 7.68/2.84  tff(c_8750, plain, (k2_pre_topc('#skF_2', k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'))=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1469, c_8739])).
% 7.68/2.84  tff(c_7072, plain, (![A_627, B_628]: (k9_subset_1(u1_struct_0(A_627), k2_pre_topc(A_627, B_628), k2_pre_topc(A_627, k3_subset_1(u1_struct_0(A_627), B_628)))=k2_tops_1(A_627, B_628) | ~m1_subset_1(B_628, k1_zfmisc_1(u1_struct_0(A_627))) | ~l1_pre_topc(A_627))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.68/2.84  tff(c_7087, plain, (![B_628]: (k9_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', B_628), k2_pre_topc('#skF_2', k3_subset_1(k2_struct_0('#skF_2'), B_628)))=k2_tops_1('#skF_2', B_628) | ~m1_subset_1(B_628, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_94, c_7072])).
% 7.68/2.84  tff(c_7095, plain, (![B_628]: (k9_subset_1(k2_struct_0('#skF_2'), k2_pre_topc('#skF_2', B_628), k2_pre_topc('#skF_2', k3_subset_1(k2_struct_0('#skF_2'), B_628)))=k2_tops_1('#skF_2', B_628) | ~m1_subset_1(B_628, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_94, c_94, c_7087])).
% 7.68/2.84  tff(c_8759, plain, (k9_subset_1(k2_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), k2_struct_0('#skF_2'))=k2_tops_1('#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_8750, c_7095])).
% 7.68/2.84  tff(c_8766, plain, (k2_tops_1('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1470, c_1650, c_1673, c_1755, c_8759])).
% 7.68/2.84  tff(c_8768, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1468, c_8766])).
% 7.68/2.84  tff(c_8770, plain, (v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_1535])).
% 7.68/2.84  tff(c_1537, plain, (![A_219, A_220]: (~v1_xboole_0(A_219) | ~r2_hidden(A_220, A_219))), inference(resolution, [status(thm)], [c_71, c_1530])).
% 7.68/2.84  tff(c_1545, plain, (![A_1, B_2]: (~v1_xboole_0(A_1) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_1537])).
% 7.68/2.84  tff(c_8771, plain, (![A_735]: (~r2_hidden(A_735, '#skF_3'))), inference(splitRight, [status(thm)], [c_1535])).
% 7.68/2.84  tff(c_8782, plain, (![B_736]: (r1_tarski('#skF_3', B_736))), inference(resolution, [status(thm)], [c_6, c_8771])).
% 7.68/2.84  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.68/2.84  tff(c_8818, plain, (![B_742]: (B_742='#skF_3' | ~r1_tarski(B_742, '#skF_3'))), inference(resolution, [status(thm)], [c_8782, c_8])).
% 7.68/2.84  tff(c_8836, plain, (![A_743]: (A_743='#skF_3' | ~v1_xboole_0(A_743))), inference(resolution, [status(thm)], [c_1545, c_8818])).
% 7.68/2.84  tff(c_8840, plain, (k2_struct_0('#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_8770, c_8836])).
% 7.68/2.84  tff(c_8843, plain, (u1_struct_0('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8840, c_94])).
% 7.68/2.84  tff(c_1495, plain, (![A_205, B_206]: (k3_xboole_0(A_205, B_206)=A_205 | ~r1_tarski(A_205, B_206))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.68/2.84  tff(c_1499, plain, (![B_7]: (k3_xboole_0(B_7, B_7)=B_7)), inference(resolution, [status(thm)], [c_12, c_1495])).
% 7.68/2.84  tff(c_8892, plain, (![A_755, B_756, C_757]: (k9_subset_1(A_755, B_756, C_757)=k3_xboole_0(B_756, C_757) | ~m1_subset_1(C_757, k1_zfmisc_1(A_755)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.68/2.84  tff(c_8898, plain, (![A_16, B_756]: (k9_subset_1(A_16, B_756, A_16)=k3_xboole_0(B_756, A_16))), inference(resolution, [status(thm)], [c_71, c_8892])).
% 7.68/2.84  tff(c_8965, plain, (![A_769, B_770]: (k2_pre_topc(A_769, B_770)=B_770 | ~v4_pre_topc(B_770, A_769) | ~m1_subset_1(B_770, k1_zfmisc_1(u1_struct_0(A_769))) | ~l1_pre_topc(A_769))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.68/2.84  tff(c_8976, plain, (![B_770]: (k2_pre_topc('#skF_2', B_770)=B_770 | ~v4_pre_topc(B_770, '#skF_2') | ~m1_subset_1(B_770, k1_zfmisc_1('#skF_3')) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_8843, c_8965])).
% 7.68/2.84  tff(c_9023, plain, (![B_779]: (k2_pre_topc('#skF_2', B_779)=B_779 | ~v4_pre_topc(B_779, '#skF_2') | ~m1_subset_1(B_779, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_8976])).
% 7.68/2.84  tff(c_9035, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_71, c_9023])).
% 7.68/2.84  tff(c_9040, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_9035])).
% 7.68/2.84  tff(c_8841, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8840, c_8770])).
% 7.68/2.84  tff(c_8863, plain, (![A_746, B_747]: (m1_subset_1(k3_subset_1(A_746, B_747), k1_zfmisc_1(A_746)) | ~m1_subset_1(B_747, k1_zfmisc_1(A_746)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.68/2.84  tff(c_34, plain, (![C_31, B_30, A_29]: (~v1_xboole_0(C_31) | ~m1_subset_1(B_30, k1_zfmisc_1(C_31)) | ~r2_hidden(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.68/2.84  tff(c_9045, plain, (![A_780, A_781, B_782]: (~v1_xboole_0(A_780) | ~r2_hidden(A_781, k3_subset_1(A_780, B_782)) | ~m1_subset_1(B_782, k1_zfmisc_1(A_780)))), inference(resolution, [status(thm)], [c_8863, c_34])).
% 7.68/2.84  tff(c_9094, plain, (![A_786, B_787, B_788]: (~v1_xboole_0(A_786) | ~m1_subset_1(B_787, k1_zfmisc_1(A_786)) | r1_tarski(k3_subset_1(A_786, B_787), B_788))), inference(resolution, [status(thm)], [c_6, c_9045])).
% 7.68/2.84  tff(c_8788, plain, (![B_736]: (B_736='#skF_3' | ~r1_tarski(B_736, '#skF_3'))), inference(resolution, [status(thm)], [c_8782, c_8])).
% 7.68/2.84  tff(c_9121, plain, (![A_789, B_790]: (k3_subset_1(A_789, B_790)='#skF_3' | ~v1_xboole_0(A_789) | ~m1_subset_1(B_790, k1_zfmisc_1(A_789)))), inference(resolution, [status(thm)], [c_9094, c_8788])).
% 7.68/2.84  tff(c_9161, plain, (![A_793]: (k3_subset_1(A_793, A_793)='#skF_3' | ~v1_xboole_0(A_793))), inference(resolution, [status(thm)], [c_71, c_9121])).
% 7.68/2.84  tff(c_9164, plain, (k3_subset_1('#skF_3', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_8841, c_9161])).
% 7.68/2.84  tff(c_10582, plain, (![A_899, B_900]: (k9_subset_1(u1_struct_0(A_899), k2_pre_topc(A_899, B_900), k2_pre_topc(A_899, k3_subset_1(u1_struct_0(A_899), B_900)))=k2_tops_1(A_899, B_900) | ~m1_subset_1(B_900, k1_zfmisc_1(u1_struct_0(A_899))) | ~l1_pre_topc(A_899))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.68/2.84  tff(c_10603, plain, (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3')))=k2_tops_1('#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_9040, c_10582])).
% 7.68/2.84  tff(c_10613, plain, (k2_tops_1('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_71, c_8843, c_1499, c_8898, c_9040, c_9164, c_8843, c_8843, c_10603])).
% 7.68/2.84  tff(c_10615, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1468, c_10613])).
% 7.68/2.84  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.68/2.84  
% 7.68/2.84  Inference rules
% 7.68/2.84  ----------------------
% 7.68/2.84  #Ref     : 0
% 7.68/2.84  #Sup     : 2406
% 7.68/2.84  #Fact    : 0
% 7.68/2.84  #Define  : 0
% 7.68/2.84  #Split   : 32
% 7.68/2.84  #Chain   : 0
% 7.68/2.84  #Close   : 0
% 7.68/2.84  
% 7.68/2.84  Ordering : KBO
% 7.68/2.84  
% 7.68/2.84  Simplification rules
% 7.68/2.84  ----------------------
% 7.68/2.84  #Subsume      : 660
% 7.68/2.84  #Demod        : 862
% 7.68/2.84  #Tautology    : 588
% 7.68/2.84  #SimpNegUnit  : 73
% 7.68/2.84  #BackRed      : 11
% 7.68/2.84  
% 7.68/2.84  #Partial instantiations: 0
% 7.68/2.84  #Strategies tried      : 1
% 7.68/2.84  
% 7.68/2.84  Timing (in seconds)
% 7.68/2.84  ----------------------
% 7.68/2.84  Preprocessing        : 0.35
% 7.68/2.84  Parsing              : 0.19
% 7.68/2.84  CNF conversion       : 0.02
% 7.68/2.84  Main loop            : 1.71
% 7.68/2.84  Inferencing          : 0.55
% 7.68/2.84  Reduction            : 0.49
% 7.68/2.84  Demodulation         : 0.32
% 7.68/2.84  BG Simplification    : 0.06
% 7.68/2.84  Subsumption          : 0.48
% 7.68/2.84  Abstraction          : 0.08
% 7.68/2.84  MUC search           : 0.00
% 7.68/2.84  Cooper               : 0.00
% 7.68/2.84  Total                : 2.10
% 7.68/2.84  Index Insertion      : 0.00
% 7.68/2.84  Index Deletion       : 0.00
% 7.68/2.84  Index Matching       : 0.00
% 7.68/2.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
