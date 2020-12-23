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
% DateTime   : Thu Dec  3 10:21:51 EST 2020

% Result     : Theorem 6.72s
% Output     : CNFRefutation 6.72s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 186 expanded)
%              Number of leaves         :   31 (  77 expanded)
%              Depth                    :   13
%              Number of atoms          :  214 ( 550 expanded)
%              Number of equality atoms :   29 (  70 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_mcart_1 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_131,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r1_tarski(C,B)
                      & v3_pre_topc(C,A) )
                   => C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tops_1)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_112,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_103,axiom,(
    ! [A] :
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

tff(f_54,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_70,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_mcart_1(C,D,E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).

tff(c_50,plain,
    ( k1_xboole_0 != '#skF_5'
    | ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_72,plain,(
    ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_46,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_199,plain,(
    ! [A_90,B_91] :
      ( r1_tarski(k1_tops_1(A_90,B_91),B_91)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ l1_pre_topc(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_204,plain,
    ( r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_199])).

tff(c_211,plain,(
    r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_204])).

tff(c_48,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_679,plain,(
    ! [A_135,B_136] :
      ( v3_pre_topc(k1_tops_1(A_135,B_136),A_135)
      | ~ m1_subset_1(B_136,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ l1_pre_topc(A_135)
      | ~ v2_pre_topc(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_687,plain,
    ( v3_pre_topc(k1_tops_1('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_679])).

tff(c_695,plain,(
    v3_pre_topc(k1_tops_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_687])).

tff(c_81,plain,(
    ! [A_68,B_69] :
      ( r1_tarski(A_68,B_69)
      | ~ m1_subset_1(A_68,k1_zfmisc_1(B_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_92,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_44,c_81])).

tff(c_129,plain,(
    ! [A_74,C_75,B_76] :
      ( r1_tarski(A_74,C_75)
      | ~ r1_tarski(B_76,C_75)
      | ~ r1_tarski(A_74,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_136,plain,(
    ! [A_74] :
      ( r1_tarski(A_74,u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_74,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_92,c_129])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_68,plain,(
    ! [C_59] :
      ( v2_tops_1('#skF_4','#skF_3')
      | k1_xboole_0 = C_59
      | ~ v3_pre_topc(C_59,'#skF_3')
      | ~ r1_tarski(C_59,'#skF_4')
      | ~ m1_subset_1(C_59,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_241,plain,(
    ! [C_94] :
      ( k1_xboole_0 = C_94
      | ~ v3_pre_topc(C_94,'#skF_3')
      | ~ r1_tarski(C_94,'#skF_4')
      | ~ m1_subset_1(C_94,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_68])).

tff(c_575,plain,(
    ! [A_126] :
      ( k1_xboole_0 = A_126
      | ~ v3_pre_topc(A_126,'#skF_3')
      | ~ r1_tarski(A_126,'#skF_4')
      | ~ r1_tarski(A_126,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_14,c_241])).

tff(c_605,plain,(
    ! [A_74] :
      ( k1_xboole_0 = A_74
      | ~ v3_pre_topc(A_74,'#skF_3')
      | ~ r1_tarski(A_74,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_136,c_575])).

tff(c_699,plain,
    ( k1_tops_1('#skF_3','#skF_4') = k1_xboole_0
    | ~ r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_695,c_605])).

tff(c_702,plain,(
    k1_tops_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_699])).

tff(c_800,plain,(
    ! [B_145,A_146] :
      ( v2_tops_1(B_145,A_146)
      | k1_tops_1(A_146,B_145) != k1_xboole_0
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0(A_146)))
      | ~ l1_pre_topc(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_811,plain,
    ( v2_tops_1('#skF_4','#skF_3')
    | k1_tops_1('#skF_3','#skF_4') != k1_xboole_0
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_800])).

tff(c_820,plain,(
    v2_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_702,c_811])).

tff(c_822,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_820])).

tff(c_823,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_824,plain,(
    v2_tops_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_52,plain,
    ( v3_pre_topc('#skF_5','#skF_3')
    | ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_826,plain,(
    v3_pre_topc('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_824,c_52])).

tff(c_54,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_834,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_824,c_54])).

tff(c_56,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_874,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_824,c_56])).

tff(c_10,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_836,plain,(
    ! [A_151,B_152] :
      ( r1_tarski(A_151,B_152)
      | ~ m1_subset_1(A_151,k1_zfmisc_1(B_152)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_844,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(resolution,[status(thm)],[c_10,c_836])).

tff(c_965,plain,(
    ! [A_170,B_171] :
      ( r1_tarski(k1_tops_1(A_170,B_171),B_171)
      | ~ m1_subset_1(B_171,k1_zfmisc_1(u1_struct_0(A_170)))
      | ~ l1_pre_topc(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1014,plain,(
    ! [A_175] :
      ( r1_tarski(k1_tops_1(A_175,k1_xboole_0),k1_xboole_0)
      | ~ l1_pre_topc(A_175) ) ),
    inference(resolution,[status(thm)],[c_10,c_965])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1023,plain,(
    ! [A_175] :
      ( k1_tops_1(A_175,k1_xboole_0) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,k1_tops_1(A_175,k1_xboole_0))
      | ~ l1_pre_topc(A_175) ) ),
    inference(resolution,[status(thm)],[c_1014,c_2])).

tff(c_1030,plain,(
    ! [A_176] :
      ( k1_tops_1(A_176,k1_xboole_0) = k1_xboole_0
      | ~ l1_pre_topc(A_176) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_844,c_1023])).

tff(c_1034,plain,(
    k1_tops_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_1030])).

tff(c_1712,plain,(
    ! [A_234,B_235,C_236] :
      ( r1_tarski('#skF_2'(A_234,B_235,C_236),C_236)
      | ~ r2_hidden(B_235,k1_tops_1(A_234,C_236))
      | ~ m1_subset_1(C_236,k1_zfmisc_1(u1_struct_0(A_234)))
      | ~ l1_pre_topc(A_234)
      | ~ v2_pre_topc(A_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1716,plain,(
    ! [B_235] :
      ( r1_tarski('#skF_2'('#skF_3',B_235,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(B_235,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1034,c_1712])).

tff(c_1793,plain,(
    ! [B_240] :
      ( r1_tarski('#skF_2'('#skF_3',B_240,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(B_240,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_10,c_1716])).

tff(c_897,plain,(
    ! [A_159,C_160,B_161] :
      ( r1_tarski(A_159,C_160)
      | ~ r1_tarski(B_161,C_160)
      | ~ r1_tarski(A_159,B_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_910,plain,(
    ! [A_159,A_6] :
      ( r1_tarski(A_159,A_6)
      | ~ r1_tarski(A_159,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_844,c_897])).

tff(c_1823,plain,(
    ! [B_240,A_6] :
      ( r1_tarski('#skF_2'('#skF_3',B_240,k1_xboole_0),A_6)
      | ~ r2_hidden(B_240,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1793,c_910])).

tff(c_1853,plain,(
    ! [B_245,A_246,C_247] :
      ( r2_hidden(B_245,'#skF_2'(A_246,B_245,C_247))
      | ~ r2_hidden(B_245,k1_tops_1(A_246,C_247))
      | ~ m1_subset_1(C_247,k1_zfmisc_1(u1_struct_0(A_246)))
      | ~ l1_pre_topc(A_246)
      | ~ v2_pre_topc(A_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1857,plain,(
    ! [B_245] :
      ( r2_hidden(B_245,'#skF_2'('#skF_3',B_245,k1_xboole_0))
      | ~ r2_hidden(B_245,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1034,c_1853])).

tff(c_1920,plain,(
    ! [B_251] :
      ( r2_hidden(B_251,'#skF_2'('#skF_3',B_251,k1_xboole_0))
      | ~ r2_hidden(B_251,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_10,c_1857])).

tff(c_18,plain,(
    ! [B_13,A_12] :
      ( ~ r1_tarski(B_13,A_12)
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1995,plain,(
    ! [B_254] :
      ( ~ r1_tarski('#skF_2'('#skF_3',B_254,k1_xboole_0),B_254)
      | ~ r2_hidden(B_254,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1920,c_18])).

tff(c_2012,plain,(
    ! [A_6] : ~ r2_hidden(A_6,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1823,c_1995])).

tff(c_1282,plain,(
    ! [A_213,B_214] :
      ( k1_tops_1(A_213,B_214) = k1_xboole_0
      | ~ v2_tops_1(B_214,A_213)
      | ~ m1_subset_1(B_214,k1_zfmisc_1(u1_struct_0(A_213)))
      | ~ l1_pre_topc(A_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1296,plain,
    ( k1_tops_1('#skF_3','#skF_4') = k1_xboole_0
    | ~ v2_tops_1('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_1282])).

tff(c_1309,plain,(
    k1_tops_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_824,c_1296])).

tff(c_20,plain,(
    ! [A_14] :
      ( r2_hidden('#skF_1'(A_14),A_14)
      | k1_xboole_0 = A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2154,plain,(
    ! [B_269,A_270,C_271,D_272] :
      ( r2_hidden(B_269,k1_tops_1(A_270,C_271))
      | ~ r2_hidden(B_269,D_272)
      | ~ r1_tarski(D_272,C_271)
      | ~ v3_pre_topc(D_272,A_270)
      | ~ m1_subset_1(D_272,k1_zfmisc_1(u1_struct_0(A_270)))
      | ~ m1_subset_1(C_271,k1_zfmisc_1(u1_struct_0(A_270)))
      | ~ l1_pre_topc(A_270)
      | ~ v2_pre_topc(A_270) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_5847,plain,(
    ! [A_422,A_423,C_424] :
      ( r2_hidden('#skF_1'(A_422),k1_tops_1(A_423,C_424))
      | ~ r1_tarski(A_422,C_424)
      | ~ v3_pre_topc(A_422,A_423)
      | ~ m1_subset_1(A_422,k1_zfmisc_1(u1_struct_0(A_423)))
      | ~ m1_subset_1(C_424,k1_zfmisc_1(u1_struct_0(A_423)))
      | ~ l1_pre_topc(A_423)
      | ~ v2_pre_topc(A_423)
      | k1_xboole_0 = A_422 ) ),
    inference(resolution,[status(thm)],[c_20,c_2154])).

tff(c_5892,plain,(
    ! [A_422] :
      ( r2_hidden('#skF_1'(A_422),k1_xboole_0)
      | ~ r1_tarski(A_422,'#skF_4')
      | ~ v3_pre_topc(A_422,'#skF_3')
      | ~ m1_subset_1(A_422,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | k1_xboole_0 = A_422 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1309,c_5847])).

tff(c_5915,plain,(
    ! [A_422] :
      ( r2_hidden('#skF_1'(A_422),k1_xboole_0)
      | ~ r1_tarski(A_422,'#skF_4')
      | ~ v3_pre_topc(A_422,'#skF_3')
      | ~ m1_subset_1(A_422,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | k1_xboole_0 = A_422 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_5892])).

tff(c_6005,plain,(
    ! [A_426] :
      ( ~ r1_tarski(A_426,'#skF_4')
      | ~ v3_pre_topc(A_426,'#skF_3')
      | ~ m1_subset_1(A_426,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | k1_xboole_0 = A_426 ) ),
    inference(negUnitSimplification,[status(thm)],[c_2012,c_5915])).

tff(c_6024,plain,
    ( ~ r1_tarski('#skF_5','#skF_4')
    | ~ v3_pre_topc('#skF_5','#skF_3')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_874,c_6005])).

tff(c_6044,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_826,c_834,c_6024])).

tff(c_6046,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_823,c_6044])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:56:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.72/2.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.72/2.37  
% 6.72/2.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.72/2.37  %$ v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_mcart_1 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 6.72/2.37  
% 6.72/2.37  %Foreground sorts:
% 6.72/2.37  
% 6.72/2.37  
% 6.72/2.37  %Background operators:
% 6.72/2.37  
% 6.72/2.37  
% 6.72/2.37  %Foreground operators:
% 6.72/2.37  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 6.72/2.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.72/2.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.72/2.37  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.72/2.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.72/2.37  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 6.72/2.37  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.72/2.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.72/2.37  tff('#skF_5', type, '#skF_5': $i).
% 6.72/2.37  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 6.72/2.37  tff('#skF_3', type, '#skF_3': $i).
% 6.72/2.37  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.72/2.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.72/2.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.72/2.37  tff('#skF_4', type, '#skF_4': $i).
% 6.72/2.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.72/2.37  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.72/2.37  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.72/2.37  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 6.72/2.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.72/2.37  
% 6.72/2.39  tff(f_131, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tops_1)).
% 6.72/2.39  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 6.72/2.39  tff(f_78, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 6.72/2.39  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.72/2.39  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 6.72/2.39  tff(f_112, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 6.72/2.39  tff(f_39, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 6.72/2.39  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.72/2.39  tff(f_103, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B, C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k1_tops_1(A, C)) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_tops_1)).
% 6.72/2.39  tff(f_54, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 6.72/2.39  tff(f_70, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_mcart_1(C, D, E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_mcart_1)).
% 6.72/2.39  tff(c_50, plain, (k1_xboole_0!='#skF_5' | ~v2_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_131])).
% 6.72/2.39  tff(c_72, plain, (~v2_tops_1('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_50])).
% 6.72/2.39  tff(c_46, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_131])).
% 6.72/2.39  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 6.72/2.39  tff(c_199, plain, (![A_90, B_91]: (r1_tarski(k1_tops_1(A_90, B_91), B_91) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0(A_90))) | ~l1_pre_topc(A_90))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.72/2.39  tff(c_204, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_44, c_199])).
% 6.72/2.39  tff(c_211, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_204])).
% 6.72/2.39  tff(c_48, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_131])).
% 6.72/2.39  tff(c_679, plain, (![A_135, B_136]: (v3_pre_topc(k1_tops_1(A_135, B_136), A_135) | ~m1_subset_1(B_136, k1_zfmisc_1(u1_struct_0(A_135))) | ~l1_pre_topc(A_135) | ~v2_pre_topc(A_135))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.72/2.39  tff(c_687, plain, (v3_pre_topc(k1_tops_1('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_44, c_679])).
% 6.72/2.39  tff(c_695, plain, (v3_pre_topc(k1_tops_1('#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_687])).
% 6.72/2.39  tff(c_81, plain, (![A_68, B_69]: (r1_tarski(A_68, B_69) | ~m1_subset_1(A_68, k1_zfmisc_1(B_69)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.72/2.39  tff(c_92, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_81])).
% 6.72/2.39  tff(c_129, plain, (![A_74, C_75, B_76]: (r1_tarski(A_74, C_75) | ~r1_tarski(B_76, C_75) | ~r1_tarski(A_74, B_76))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.72/2.39  tff(c_136, plain, (![A_74]: (r1_tarski(A_74, u1_struct_0('#skF_3')) | ~r1_tarski(A_74, '#skF_4'))), inference(resolution, [status(thm)], [c_92, c_129])).
% 6.72/2.39  tff(c_14, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.72/2.39  tff(c_68, plain, (![C_59]: (v2_tops_1('#skF_4', '#skF_3') | k1_xboole_0=C_59 | ~v3_pre_topc(C_59, '#skF_3') | ~r1_tarski(C_59, '#skF_4') | ~m1_subset_1(C_59, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_131])).
% 6.72/2.39  tff(c_241, plain, (![C_94]: (k1_xboole_0=C_94 | ~v3_pre_topc(C_94, '#skF_3') | ~r1_tarski(C_94, '#skF_4') | ~m1_subset_1(C_94, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_72, c_68])).
% 6.72/2.39  tff(c_575, plain, (![A_126]: (k1_xboole_0=A_126 | ~v3_pre_topc(A_126, '#skF_3') | ~r1_tarski(A_126, '#skF_4') | ~r1_tarski(A_126, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_14, c_241])).
% 6.72/2.39  tff(c_605, plain, (![A_74]: (k1_xboole_0=A_74 | ~v3_pre_topc(A_74, '#skF_3') | ~r1_tarski(A_74, '#skF_4'))), inference(resolution, [status(thm)], [c_136, c_575])).
% 6.72/2.39  tff(c_699, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0 | ~r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_695, c_605])).
% 6.72/2.39  tff(c_702, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_211, c_699])).
% 6.72/2.39  tff(c_800, plain, (![B_145, A_146]: (v2_tops_1(B_145, A_146) | k1_tops_1(A_146, B_145)!=k1_xboole_0 | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0(A_146))) | ~l1_pre_topc(A_146))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.72/2.39  tff(c_811, plain, (v2_tops_1('#skF_4', '#skF_3') | k1_tops_1('#skF_3', '#skF_4')!=k1_xboole_0 | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_44, c_800])).
% 6.72/2.39  tff(c_820, plain, (v2_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_702, c_811])).
% 6.72/2.39  tff(c_822, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_820])).
% 6.72/2.39  tff(c_823, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_50])).
% 6.72/2.39  tff(c_824, plain, (v2_tops_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_50])).
% 6.72/2.39  tff(c_52, plain, (v3_pre_topc('#skF_5', '#skF_3') | ~v2_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_131])).
% 6.72/2.39  tff(c_826, plain, (v3_pre_topc('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_824, c_52])).
% 6.72/2.39  tff(c_54, plain, (r1_tarski('#skF_5', '#skF_4') | ~v2_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_131])).
% 6.72/2.39  tff(c_834, plain, (r1_tarski('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_824, c_54])).
% 6.72/2.39  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_131])).
% 6.72/2.39  tff(c_874, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_824, c_56])).
% 6.72/2.39  tff(c_10, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.72/2.39  tff(c_836, plain, (![A_151, B_152]: (r1_tarski(A_151, B_152) | ~m1_subset_1(A_151, k1_zfmisc_1(B_152)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.72/2.39  tff(c_844, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(resolution, [status(thm)], [c_10, c_836])).
% 6.72/2.39  tff(c_965, plain, (![A_170, B_171]: (r1_tarski(k1_tops_1(A_170, B_171), B_171) | ~m1_subset_1(B_171, k1_zfmisc_1(u1_struct_0(A_170))) | ~l1_pre_topc(A_170))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.72/2.39  tff(c_1014, plain, (![A_175]: (r1_tarski(k1_tops_1(A_175, k1_xboole_0), k1_xboole_0) | ~l1_pre_topc(A_175))), inference(resolution, [status(thm)], [c_10, c_965])).
% 6.72/2.39  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.72/2.39  tff(c_1023, plain, (![A_175]: (k1_tops_1(A_175, k1_xboole_0)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k1_tops_1(A_175, k1_xboole_0)) | ~l1_pre_topc(A_175))), inference(resolution, [status(thm)], [c_1014, c_2])).
% 6.72/2.39  tff(c_1030, plain, (![A_176]: (k1_tops_1(A_176, k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc(A_176))), inference(demodulation, [status(thm), theory('equality')], [c_844, c_1023])).
% 6.72/2.39  tff(c_1034, plain, (k1_tops_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_46, c_1030])).
% 6.72/2.39  tff(c_1712, plain, (![A_234, B_235, C_236]: (r1_tarski('#skF_2'(A_234, B_235, C_236), C_236) | ~r2_hidden(B_235, k1_tops_1(A_234, C_236)) | ~m1_subset_1(C_236, k1_zfmisc_1(u1_struct_0(A_234))) | ~l1_pre_topc(A_234) | ~v2_pre_topc(A_234))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.72/2.39  tff(c_1716, plain, (![B_235]: (r1_tarski('#skF_2'('#skF_3', B_235, k1_xboole_0), k1_xboole_0) | ~r2_hidden(B_235, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1034, c_1712])).
% 6.72/2.39  tff(c_1793, plain, (![B_240]: (r1_tarski('#skF_2'('#skF_3', B_240, k1_xboole_0), k1_xboole_0) | ~r2_hidden(B_240, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_10, c_1716])).
% 6.72/2.39  tff(c_897, plain, (![A_159, C_160, B_161]: (r1_tarski(A_159, C_160) | ~r1_tarski(B_161, C_160) | ~r1_tarski(A_159, B_161))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.72/2.39  tff(c_910, plain, (![A_159, A_6]: (r1_tarski(A_159, A_6) | ~r1_tarski(A_159, k1_xboole_0))), inference(resolution, [status(thm)], [c_844, c_897])).
% 6.72/2.39  tff(c_1823, plain, (![B_240, A_6]: (r1_tarski('#skF_2'('#skF_3', B_240, k1_xboole_0), A_6) | ~r2_hidden(B_240, k1_xboole_0))), inference(resolution, [status(thm)], [c_1793, c_910])).
% 6.72/2.39  tff(c_1853, plain, (![B_245, A_246, C_247]: (r2_hidden(B_245, '#skF_2'(A_246, B_245, C_247)) | ~r2_hidden(B_245, k1_tops_1(A_246, C_247)) | ~m1_subset_1(C_247, k1_zfmisc_1(u1_struct_0(A_246))) | ~l1_pre_topc(A_246) | ~v2_pre_topc(A_246))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.72/2.39  tff(c_1857, plain, (![B_245]: (r2_hidden(B_245, '#skF_2'('#skF_3', B_245, k1_xboole_0)) | ~r2_hidden(B_245, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1034, c_1853])).
% 6.72/2.39  tff(c_1920, plain, (![B_251]: (r2_hidden(B_251, '#skF_2'('#skF_3', B_251, k1_xboole_0)) | ~r2_hidden(B_251, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_10, c_1857])).
% 6.72/2.39  tff(c_18, plain, (![B_13, A_12]: (~r1_tarski(B_13, A_12) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.72/2.39  tff(c_1995, plain, (![B_254]: (~r1_tarski('#skF_2'('#skF_3', B_254, k1_xboole_0), B_254) | ~r2_hidden(B_254, k1_xboole_0))), inference(resolution, [status(thm)], [c_1920, c_18])).
% 6.72/2.39  tff(c_2012, plain, (![A_6]: (~r2_hidden(A_6, k1_xboole_0))), inference(resolution, [status(thm)], [c_1823, c_1995])).
% 6.72/2.39  tff(c_1282, plain, (![A_213, B_214]: (k1_tops_1(A_213, B_214)=k1_xboole_0 | ~v2_tops_1(B_214, A_213) | ~m1_subset_1(B_214, k1_zfmisc_1(u1_struct_0(A_213))) | ~l1_pre_topc(A_213))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.72/2.39  tff(c_1296, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0 | ~v2_tops_1('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_44, c_1282])).
% 6.72/2.39  tff(c_1309, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_46, c_824, c_1296])).
% 6.72/2.39  tff(c_20, plain, (![A_14]: (r2_hidden('#skF_1'(A_14), A_14) | k1_xboole_0=A_14)), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.72/2.39  tff(c_2154, plain, (![B_269, A_270, C_271, D_272]: (r2_hidden(B_269, k1_tops_1(A_270, C_271)) | ~r2_hidden(B_269, D_272) | ~r1_tarski(D_272, C_271) | ~v3_pre_topc(D_272, A_270) | ~m1_subset_1(D_272, k1_zfmisc_1(u1_struct_0(A_270))) | ~m1_subset_1(C_271, k1_zfmisc_1(u1_struct_0(A_270))) | ~l1_pre_topc(A_270) | ~v2_pre_topc(A_270))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.72/2.39  tff(c_5847, plain, (![A_422, A_423, C_424]: (r2_hidden('#skF_1'(A_422), k1_tops_1(A_423, C_424)) | ~r1_tarski(A_422, C_424) | ~v3_pre_topc(A_422, A_423) | ~m1_subset_1(A_422, k1_zfmisc_1(u1_struct_0(A_423))) | ~m1_subset_1(C_424, k1_zfmisc_1(u1_struct_0(A_423))) | ~l1_pre_topc(A_423) | ~v2_pre_topc(A_423) | k1_xboole_0=A_422)), inference(resolution, [status(thm)], [c_20, c_2154])).
% 6.72/2.39  tff(c_5892, plain, (![A_422]: (r2_hidden('#skF_1'(A_422), k1_xboole_0) | ~r1_tarski(A_422, '#skF_4') | ~v3_pre_topc(A_422, '#skF_3') | ~m1_subset_1(A_422, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | k1_xboole_0=A_422)), inference(superposition, [status(thm), theory('equality')], [c_1309, c_5847])).
% 6.72/2.39  tff(c_5915, plain, (![A_422]: (r2_hidden('#skF_1'(A_422), k1_xboole_0) | ~r1_tarski(A_422, '#skF_4') | ~v3_pre_topc(A_422, '#skF_3') | ~m1_subset_1(A_422, k1_zfmisc_1(u1_struct_0('#skF_3'))) | k1_xboole_0=A_422)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_5892])).
% 6.72/2.39  tff(c_6005, plain, (![A_426]: (~r1_tarski(A_426, '#skF_4') | ~v3_pre_topc(A_426, '#skF_3') | ~m1_subset_1(A_426, k1_zfmisc_1(u1_struct_0('#skF_3'))) | k1_xboole_0=A_426)), inference(negUnitSimplification, [status(thm)], [c_2012, c_5915])).
% 6.72/2.39  tff(c_6024, plain, (~r1_tarski('#skF_5', '#skF_4') | ~v3_pre_topc('#skF_5', '#skF_3') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_874, c_6005])).
% 6.72/2.39  tff(c_6044, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_826, c_834, c_6024])).
% 6.72/2.39  tff(c_6046, plain, $false, inference(negUnitSimplification, [status(thm)], [c_823, c_6044])).
% 6.72/2.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.72/2.39  
% 6.72/2.39  Inference rules
% 6.72/2.39  ----------------------
% 6.72/2.39  #Ref     : 0
% 6.72/2.39  #Sup     : 1331
% 6.72/2.39  #Fact    : 0
% 6.72/2.39  #Define  : 0
% 6.72/2.39  #Split   : 23
% 6.72/2.39  #Chain   : 0
% 6.72/2.39  #Close   : 0
% 6.72/2.39  
% 6.72/2.39  Ordering : KBO
% 6.72/2.39  
% 6.72/2.39  Simplification rules
% 6.72/2.39  ----------------------
% 6.72/2.39  #Subsume      : 576
% 6.72/2.39  #Demod        : 586
% 6.72/2.39  #Tautology    : 250
% 6.72/2.39  #SimpNegUnit  : 39
% 6.72/2.39  #BackRed      : 12
% 6.72/2.39  
% 6.72/2.39  #Partial instantiations: 0
% 6.72/2.39  #Strategies tried      : 1
% 6.72/2.39  
% 6.72/2.39  Timing (in seconds)
% 6.72/2.39  ----------------------
% 6.72/2.39  Preprocessing        : 0.34
% 6.72/2.39  Parsing              : 0.18
% 6.72/2.39  CNF conversion       : 0.03
% 6.72/2.39  Main loop            : 1.24
% 6.72/2.39  Inferencing          : 0.38
% 6.72/2.39  Reduction            : 0.39
% 6.72/2.39  Demodulation         : 0.25
% 6.72/2.39  BG Simplification    : 0.04
% 6.72/2.39  Subsumption          : 0.34
% 6.72/2.39  Abstraction          : 0.05
% 6.72/2.39  MUC search           : 0.00
% 6.72/2.39  Cooper               : 0.00
% 6.72/2.39  Total                : 1.62
% 6.72/2.39  Index Insertion      : 0.00
% 6.72/2.39  Index Deletion       : 0.00
% 6.72/2.39  Index Matching       : 0.00
% 6.72/2.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
