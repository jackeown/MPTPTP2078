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
% DateTime   : Thu Dec  3 10:26:37 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.46s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 240 expanded)
%              Number of leaves         :   27 (  86 expanded)
%              Depth                    :   15
%              Number of atoms          :  222 ( 930 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   14 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k4_xboole_0 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(f_128,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,A) )
                   => ( m1_pre_topc(B,C)
                     => ( ( ~ r1_tsep_1(C,D)
                          & ~ r1_tsep_1(D,C) )
                        | ( r1_tsep_1(B,D)
                          & r1_tsep_1(D,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tmap_1)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(f_48,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_90,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(c_48,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_36,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_913,plain,(
    ! [B_165,A_166] :
      ( l1_pre_topc(B_165)
      | ~ m1_pre_topc(B_165,A_166)
      | ~ l1_pre_topc(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_922,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_913])).

tff(c_932,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_922])).

tff(c_16,plain,(
    ! [A_11] :
      ( l1_struct_0(A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_44,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_916,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_913])).

tff(c_928,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_916])).

tff(c_40,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_819,plain,(
    ! [B_152,A_153] :
      ( l1_pre_topc(B_152)
      | ~ m1_pre_topc(B_152,A_153)
      | ~ l1_pre_topc(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_831,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_819])).

tff(c_841,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_831])).

tff(c_828,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_819])).

tff(c_838,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_828])).

tff(c_59,plain,(
    ! [B_42,A_43] :
      ( l1_pre_topc(B_42)
      | ~ m1_pre_topc(B_42,A_43)
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_62,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_59])).

tff(c_74,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_62])).

tff(c_34,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_68,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_59])).

tff(c_78,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_68])).

tff(c_71,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_59])).

tff(c_81,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_71])).

tff(c_32,plain,
    ( r1_tsep_1('#skF_4','#skF_3')
    | r1_tsep_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_57,plain,(
    r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_145,plain,(
    ! [B_56,A_57] :
      ( r1_tsep_1(B_56,A_57)
      | ~ r1_tsep_1(A_57,B_56)
      | ~ l1_struct_0(B_56)
      | ~ l1_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_148,plain,
    ( r1_tsep_1('#skF_4','#skF_3')
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_57,c_145])).

tff(c_149,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_148])).

tff(c_152,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_149])).

tff(c_156,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_152])).

tff(c_157,plain,
    ( ~ l1_struct_0('#skF_4')
    | r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_164,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_157])).

tff(c_167,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_164])).

tff(c_171,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_167])).

tff(c_173,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_157])).

tff(c_172,plain,(
    r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_157])).

tff(c_158,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_50,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_100,plain,(
    ! [B_51,A_52] :
      ( v2_pre_topc(B_51)
      | ~ m1_pre_topc(B_51,A_52)
      | ~ l1_pre_topc(A_52)
      | ~ v2_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_112,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_100])).

tff(c_124,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_112])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_345,plain,(
    ! [B_99,C_100,A_101] :
      ( m1_pre_topc(B_99,C_100)
      | ~ r1_tarski(u1_struct_0(B_99),u1_struct_0(C_100))
      | ~ m1_pre_topc(C_100,A_101)
      | ~ m1_pre_topc(B_99,A_101)
      | ~ l1_pre_topc(A_101)
      | ~ v2_pre_topc(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_362,plain,(
    ! [B_102,A_103] :
      ( m1_pre_topc(B_102,B_102)
      | ~ m1_pre_topc(B_102,A_103)
      | ~ l1_pre_topc(A_103)
      | ~ v2_pre_topc(A_103) ) ),
    inference(resolution,[status(thm)],[c_6,c_345])).

tff(c_370,plain,
    ( m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_362])).

tff(c_382,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_370])).

tff(c_26,plain,(
    ! [B_24,C_26,A_20] :
      ( r1_tarski(u1_struct_0(B_24),u1_struct_0(C_26))
      | ~ m1_pre_topc(B_24,C_26)
      | ~ m1_pre_topc(C_26,A_20)
      | ~ m1_pre_topc(B_24,A_20)
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_431,plain,(
    ! [B_24] :
      ( r1_tarski(u1_struct_0(B_24),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_24,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_382,c_26])).

tff(c_443,plain,(
    ! [B_24] :
      ( r1_tarski(u1_struct_0(B_24),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_24,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_81,c_431])).

tff(c_159,plain,(
    ! [A_58,B_59] :
      ( r1_xboole_0(u1_struct_0(A_58),u1_struct_0(B_59))
      | ~ r1_tsep_1(A_58,B_59)
      | ~ l1_struct_0(B_59)
      | ~ l1_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = A_3
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_618,plain,(
    ! [A_113,B_114] :
      ( k4_xboole_0(u1_struct_0(A_113),u1_struct_0(B_114)) = u1_struct_0(A_113)
      | ~ r1_tsep_1(A_113,B_114)
      | ~ l1_struct_0(B_114)
      | ~ l1_struct_0(A_113) ) ),
    inference(resolution,[status(thm)],[c_159,c_8])).

tff(c_12,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_xboole_0(A_5,k4_xboole_0(C_7,B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_746,plain,(
    ! [A_138,A_139,B_140] :
      ( r1_xboole_0(A_138,u1_struct_0(A_139))
      | ~ r1_tarski(A_138,u1_struct_0(B_140))
      | ~ r1_tsep_1(A_139,B_140)
      | ~ l1_struct_0(B_140)
      | ~ l1_struct_0(A_139) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_618,c_12])).

tff(c_748,plain,(
    ! [B_24,A_139] :
      ( r1_xboole_0(u1_struct_0(B_24),u1_struct_0(A_139))
      | ~ r1_tsep_1(A_139,'#skF_3')
      | ~ l1_struct_0('#skF_3')
      | ~ l1_struct_0(A_139)
      | ~ m1_pre_topc(B_24,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_443,c_746])).

tff(c_773,plain,(
    ! [B_143,A_144] :
      ( r1_xboole_0(u1_struct_0(B_143),u1_struct_0(A_144))
      | ~ r1_tsep_1(A_144,'#skF_3')
      | ~ l1_struct_0(A_144)
      | ~ m1_pre_topc(B_143,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_748])).

tff(c_20,plain,(
    ! [A_15,B_17] :
      ( r1_tsep_1(A_15,B_17)
      | ~ r1_xboole_0(u1_struct_0(A_15),u1_struct_0(B_17))
      | ~ l1_struct_0(B_17)
      | ~ l1_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_791,plain,(
    ! [B_147,A_148] :
      ( r1_tsep_1(B_147,A_148)
      | ~ l1_struct_0(B_147)
      | ~ r1_tsep_1(A_148,'#skF_3')
      | ~ l1_struct_0(A_148)
      | ~ m1_pre_topc(B_147,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_773,c_20])).

tff(c_793,plain,(
    ! [B_147] :
      ( r1_tsep_1(B_147,'#skF_4')
      | ~ l1_struct_0(B_147)
      | ~ l1_struct_0('#skF_4')
      | ~ m1_pre_topc(B_147,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_172,c_791])).

tff(c_797,plain,(
    ! [B_149] :
      ( r1_tsep_1(B_149,'#skF_4')
      | ~ l1_struct_0(B_149)
      | ~ m1_pre_topc(B_149,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_793])).

tff(c_30,plain,
    ( ~ r1_tsep_1('#skF_4','#skF_2')
    | ~ r1_tsep_1('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_56,plain,(
    ~ r1_tsep_1('#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_802,plain,
    ( ~ l1_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_797,c_56])).

tff(c_808,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_802])).

tff(c_811,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_808])).

tff(c_815,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_811])).

tff(c_817,plain,(
    ~ r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_816,plain,(
    r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_885,plain,(
    ! [B_163,A_164] :
      ( r1_tsep_1(B_163,A_164)
      | ~ r1_tsep_1(A_164,B_163)
      | ~ l1_struct_0(B_163)
      | ~ l1_struct_0(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_887,plain,
    ( r1_tsep_1('#skF_3','#skF_4')
    | ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_816,c_885])).

tff(c_890,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_817,c_887])).

tff(c_893,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_890])).

tff(c_896,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_893])).

tff(c_900,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_838,c_896])).

tff(c_901,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_890])).

tff(c_905,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_901])).

tff(c_909,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_841,c_905])).

tff(c_910,plain,(
    ~ r1_tsep_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_911,plain,(
    r1_tsep_1('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_986,plain,(
    ! [B_178,A_179] :
      ( r1_tsep_1(B_178,A_179)
      | ~ r1_tsep_1(A_179,B_178)
      | ~ l1_struct_0(B_178)
      | ~ l1_struct_0(A_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_990,plain,
    ( r1_tsep_1('#skF_4','#skF_2')
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_911,c_986])).

tff(c_994,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_910,c_990])).

tff(c_995,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_994])).

tff(c_1000,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_995])).

tff(c_1004,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_928,c_1000])).

tff(c_1005,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_994])).

tff(c_1009,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_1005])).

tff(c_1013,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_932,c_1009])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:09:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.06/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/1.62  
% 3.46/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/1.63  %$ r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k4_xboole_0 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.46/1.63  
% 3.46/1.63  %Foreground sorts:
% 3.46/1.63  
% 3.46/1.63  
% 3.46/1.63  %Background operators:
% 3.46/1.63  
% 3.46/1.63  
% 3.46/1.63  %Foreground operators:
% 3.46/1.63  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.46/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.46/1.63  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.46/1.63  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.46/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.46/1.63  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.46/1.63  tff('#skF_2', type, '#skF_2': $i).
% 3.46/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.46/1.63  tff('#skF_1', type, '#skF_1': $i).
% 3.46/1.63  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.46/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.46/1.63  tff('#skF_4', type, '#skF_4': $i).
% 3.46/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.46/1.63  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.46/1.63  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.46/1.63  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 3.46/1.63  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.46/1.63  
% 3.46/1.64  tff(f_128, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (m1_pre_topc(B, C) => ((~r1_tsep_1(C, D) & ~r1_tsep_1(D, C)) | (r1_tsep_1(B, D) & r1_tsep_1(D, B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tmap_1)).
% 3.46/1.64  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.46/1.64  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.46/1.64  tff(f_76, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 3.46/1.64  tff(f_48, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.46/1.64  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.46/1.64  tff(f_90, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 3.46/1.64  tff(f_68, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tsep_1)).
% 3.46/1.64  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.46/1.64  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 3.46/1.64  tff(c_48, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.46/1.64  tff(c_36, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.46/1.64  tff(c_913, plain, (![B_165, A_166]: (l1_pre_topc(B_165) | ~m1_pre_topc(B_165, A_166) | ~l1_pre_topc(A_166))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.46/1.64  tff(c_922, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_913])).
% 3.46/1.64  tff(c_932, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_922])).
% 3.46/1.64  tff(c_16, plain, (![A_11]: (l1_struct_0(A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.46/1.64  tff(c_44, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.46/1.64  tff(c_916, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_913])).
% 3.46/1.64  tff(c_928, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_916])).
% 3.46/1.64  tff(c_40, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.46/1.64  tff(c_819, plain, (![B_152, A_153]: (l1_pre_topc(B_152) | ~m1_pre_topc(B_152, A_153) | ~l1_pre_topc(A_153))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.46/1.64  tff(c_831, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_819])).
% 3.46/1.64  tff(c_841, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_831])).
% 3.46/1.64  tff(c_828, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_819])).
% 3.46/1.64  tff(c_838, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_828])).
% 3.46/1.64  tff(c_59, plain, (![B_42, A_43]: (l1_pre_topc(B_42) | ~m1_pre_topc(B_42, A_43) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.46/1.64  tff(c_62, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_59])).
% 3.46/1.64  tff(c_74, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_62])).
% 3.46/1.64  tff(c_34, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.46/1.64  tff(c_68, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_59])).
% 3.46/1.64  tff(c_78, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_68])).
% 3.46/1.64  tff(c_71, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_59])).
% 3.46/1.64  tff(c_81, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_71])).
% 3.46/1.64  tff(c_32, plain, (r1_tsep_1('#skF_4', '#skF_3') | r1_tsep_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.46/1.64  tff(c_57, plain, (r1_tsep_1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_32])).
% 3.46/1.64  tff(c_145, plain, (![B_56, A_57]: (r1_tsep_1(B_56, A_57) | ~r1_tsep_1(A_57, B_56) | ~l1_struct_0(B_56) | ~l1_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.46/1.64  tff(c_148, plain, (r1_tsep_1('#skF_4', '#skF_3') | ~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_57, c_145])).
% 3.46/1.64  tff(c_149, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_148])).
% 3.46/1.64  tff(c_152, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_16, c_149])).
% 3.46/1.64  tff(c_156, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_81, c_152])).
% 3.46/1.64  tff(c_157, plain, (~l1_struct_0('#skF_4') | r1_tsep_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_148])).
% 3.46/1.64  tff(c_164, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_157])).
% 3.46/1.64  tff(c_167, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_16, c_164])).
% 3.46/1.64  tff(c_171, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_167])).
% 3.46/1.64  tff(c_173, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_157])).
% 3.46/1.64  tff(c_172, plain, (r1_tsep_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_157])).
% 3.46/1.64  tff(c_158, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_148])).
% 3.46/1.64  tff(c_50, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.46/1.64  tff(c_100, plain, (![B_51, A_52]: (v2_pre_topc(B_51) | ~m1_pre_topc(B_51, A_52) | ~l1_pre_topc(A_52) | ~v2_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.46/1.64  tff(c_112, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_100])).
% 3.46/1.64  tff(c_124, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_112])).
% 3.46/1.64  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.46/1.64  tff(c_345, plain, (![B_99, C_100, A_101]: (m1_pre_topc(B_99, C_100) | ~r1_tarski(u1_struct_0(B_99), u1_struct_0(C_100)) | ~m1_pre_topc(C_100, A_101) | ~m1_pre_topc(B_99, A_101) | ~l1_pre_topc(A_101) | ~v2_pre_topc(A_101))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.46/1.64  tff(c_362, plain, (![B_102, A_103]: (m1_pre_topc(B_102, B_102) | ~m1_pre_topc(B_102, A_103) | ~l1_pre_topc(A_103) | ~v2_pre_topc(A_103))), inference(resolution, [status(thm)], [c_6, c_345])).
% 3.46/1.64  tff(c_370, plain, (m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_362])).
% 3.46/1.64  tff(c_382, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_370])).
% 3.46/1.64  tff(c_26, plain, (![B_24, C_26, A_20]: (r1_tarski(u1_struct_0(B_24), u1_struct_0(C_26)) | ~m1_pre_topc(B_24, C_26) | ~m1_pre_topc(C_26, A_20) | ~m1_pre_topc(B_24, A_20) | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.46/1.64  tff(c_431, plain, (![B_24]: (r1_tarski(u1_struct_0(B_24), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_24, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_382, c_26])).
% 3.46/1.64  tff(c_443, plain, (![B_24]: (r1_tarski(u1_struct_0(B_24), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_24, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_81, c_431])).
% 3.46/1.64  tff(c_159, plain, (![A_58, B_59]: (r1_xboole_0(u1_struct_0(A_58), u1_struct_0(B_59)) | ~r1_tsep_1(A_58, B_59) | ~l1_struct_0(B_59) | ~l1_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.46/1.64  tff(c_8, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=A_3 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.46/1.64  tff(c_618, plain, (![A_113, B_114]: (k4_xboole_0(u1_struct_0(A_113), u1_struct_0(B_114))=u1_struct_0(A_113) | ~r1_tsep_1(A_113, B_114) | ~l1_struct_0(B_114) | ~l1_struct_0(A_113))), inference(resolution, [status(thm)], [c_159, c_8])).
% 3.46/1.64  tff(c_12, plain, (![A_5, C_7, B_6]: (r1_xboole_0(A_5, k4_xboole_0(C_7, B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.46/1.64  tff(c_746, plain, (![A_138, A_139, B_140]: (r1_xboole_0(A_138, u1_struct_0(A_139)) | ~r1_tarski(A_138, u1_struct_0(B_140)) | ~r1_tsep_1(A_139, B_140) | ~l1_struct_0(B_140) | ~l1_struct_0(A_139))), inference(superposition, [status(thm), theory('equality')], [c_618, c_12])).
% 3.46/1.64  tff(c_748, plain, (![B_24, A_139]: (r1_xboole_0(u1_struct_0(B_24), u1_struct_0(A_139)) | ~r1_tsep_1(A_139, '#skF_3') | ~l1_struct_0('#skF_3') | ~l1_struct_0(A_139) | ~m1_pre_topc(B_24, '#skF_3'))), inference(resolution, [status(thm)], [c_443, c_746])).
% 3.46/1.64  tff(c_773, plain, (![B_143, A_144]: (r1_xboole_0(u1_struct_0(B_143), u1_struct_0(A_144)) | ~r1_tsep_1(A_144, '#skF_3') | ~l1_struct_0(A_144) | ~m1_pre_topc(B_143, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_748])).
% 3.46/1.64  tff(c_20, plain, (![A_15, B_17]: (r1_tsep_1(A_15, B_17) | ~r1_xboole_0(u1_struct_0(A_15), u1_struct_0(B_17)) | ~l1_struct_0(B_17) | ~l1_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.46/1.64  tff(c_791, plain, (![B_147, A_148]: (r1_tsep_1(B_147, A_148) | ~l1_struct_0(B_147) | ~r1_tsep_1(A_148, '#skF_3') | ~l1_struct_0(A_148) | ~m1_pre_topc(B_147, '#skF_3'))), inference(resolution, [status(thm)], [c_773, c_20])).
% 3.46/1.64  tff(c_793, plain, (![B_147]: (r1_tsep_1(B_147, '#skF_4') | ~l1_struct_0(B_147) | ~l1_struct_0('#skF_4') | ~m1_pre_topc(B_147, '#skF_3'))), inference(resolution, [status(thm)], [c_172, c_791])).
% 3.46/1.64  tff(c_797, plain, (![B_149]: (r1_tsep_1(B_149, '#skF_4') | ~l1_struct_0(B_149) | ~m1_pre_topc(B_149, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_793])).
% 3.46/1.64  tff(c_30, plain, (~r1_tsep_1('#skF_4', '#skF_2') | ~r1_tsep_1('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.46/1.64  tff(c_56, plain, (~r1_tsep_1('#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_30])).
% 3.46/1.64  tff(c_802, plain, (~l1_struct_0('#skF_2') | ~m1_pre_topc('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_797, c_56])).
% 3.46/1.64  tff(c_808, plain, (~l1_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_802])).
% 3.46/1.64  tff(c_811, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_16, c_808])).
% 3.46/1.64  tff(c_815, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_811])).
% 3.46/1.64  tff(c_817, plain, (~r1_tsep_1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_32])).
% 3.46/1.64  tff(c_816, plain, (r1_tsep_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_32])).
% 3.46/1.64  tff(c_885, plain, (![B_163, A_164]: (r1_tsep_1(B_163, A_164) | ~r1_tsep_1(A_164, B_163) | ~l1_struct_0(B_163) | ~l1_struct_0(A_164))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.46/1.64  tff(c_887, plain, (r1_tsep_1('#skF_3', '#skF_4') | ~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_816, c_885])).
% 3.46/1.64  tff(c_890, plain, (~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_817, c_887])).
% 3.46/1.64  tff(c_893, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_890])).
% 3.46/1.64  tff(c_896, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_16, c_893])).
% 3.46/1.64  tff(c_900, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_838, c_896])).
% 3.46/1.64  tff(c_901, plain, (~l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_890])).
% 3.46/1.64  tff(c_905, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_16, c_901])).
% 3.46/1.64  tff(c_909, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_841, c_905])).
% 3.46/1.64  tff(c_910, plain, (~r1_tsep_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_30])).
% 3.46/1.64  tff(c_911, plain, (r1_tsep_1('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_30])).
% 3.46/1.64  tff(c_986, plain, (![B_178, A_179]: (r1_tsep_1(B_178, A_179) | ~r1_tsep_1(A_179, B_178) | ~l1_struct_0(B_178) | ~l1_struct_0(A_179))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.46/1.64  tff(c_990, plain, (r1_tsep_1('#skF_4', '#skF_2') | ~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_911, c_986])).
% 3.46/1.64  tff(c_994, plain, (~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_910, c_990])).
% 3.46/1.64  tff(c_995, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_994])).
% 3.46/1.64  tff(c_1000, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_16, c_995])).
% 3.46/1.64  tff(c_1004, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_928, c_1000])).
% 3.46/1.64  tff(c_1005, plain, (~l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_994])).
% 3.46/1.64  tff(c_1009, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_16, c_1005])).
% 3.46/1.64  tff(c_1013, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_932, c_1009])).
% 3.46/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/1.64  
% 3.46/1.64  Inference rules
% 3.46/1.64  ----------------------
% 3.46/1.64  #Ref     : 0
% 3.46/1.64  #Sup     : 200
% 3.46/1.64  #Fact    : 0
% 3.46/1.64  #Define  : 0
% 3.46/1.64  #Split   : 11
% 3.46/1.64  #Chain   : 0
% 3.46/1.64  #Close   : 0
% 3.46/1.64  
% 3.46/1.64  Ordering : KBO
% 3.46/1.64  
% 3.46/1.65  Simplification rules
% 3.46/1.65  ----------------------
% 3.46/1.65  #Subsume      : 21
% 3.46/1.65  #Demod        : 122
% 3.46/1.65  #Tautology    : 50
% 3.46/1.65  #SimpNegUnit  : 2
% 3.46/1.65  #BackRed      : 0
% 3.46/1.65  
% 3.46/1.65  #Partial instantiations: 0
% 3.46/1.65  #Strategies tried      : 1
% 3.46/1.65  
% 3.46/1.65  Timing (in seconds)
% 3.46/1.65  ----------------------
% 3.46/1.65  Preprocessing        : 0.35
% 3.46/1.65  Parsing              : 0.20
% 3.46/1.65  CNF conversion       : 0.03
% 3.46/1.65  Main loop            : 0.45
% 3.46/1.65  Inferencing          : 0.16
% 3.46/1.65  Reduction            : 0.12
% 3.46/1.65  Demodulation         : 0.08
% 3.46/1.65  BG Simplification    : 0.03
% 3.46/1.65  Subsumption          : 0.09
% 3.46/1.65  Abstraction          : 0.02
% 3.46/1.65  MUC search           : 0.00
% 3.46/1.65  Cooper               : 0.00
% 3.46/1.65  Total                : 0.84
% 3.46/1.65  Index Insertion      : 0.00
% 3.46/1.65  Index Deletion       : 0.00
% 3.46/1.65  Index Matching       : 0.00
% 3.46/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
