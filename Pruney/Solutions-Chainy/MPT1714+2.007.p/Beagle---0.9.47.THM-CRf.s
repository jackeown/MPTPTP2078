%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:33 EST 2020

% Result     : Theorem 3.50s
% Output     : CNFRefutation 3.58s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 253 expanded)
%              Number of leaves         :   27 (  90 expanded)
%              Depth                    :   15
%              Number of atoms          :  227 ( 979 expanded)
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
                     => ( ( r1_tsep_1(B,D)
                          & r1_tsep_1(D,B) )
                        | ( ~ r1_tsep_1(C,D)
                          & ~ r1_tsep_1(D,C) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tmap_1)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(f_48,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(c_48,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_40,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_916,plain,(
    ! [B_165,A_166] :
      ( l1_pre_topc(B_165)
      | ~ m1_pre_topc(B_165,A_166)
      | ~ l1_pre_topc(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_928,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_916])).

tff(c_938,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_928])).

tff(c_34,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_932,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_916])).

tff(c_939,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_932])).

tff(c_941,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_938,c_939])).

tff(c_943,plain,(
    l1_pre_topc('#skF_3') ),
    inference(splitRight,[status(thm)],[c_932])).

tff(c_16,plain,(
    ! [A_11] :
      ( l1_struct_0(A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_36,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_925,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_916])).

tff(c_935,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_925])).

tff(c_819,plain,(
    ! [B_152,A_153] :
      ( l1_pre_topc(B_152)
      | ~ m1_pre_topc(B_152,A_153)
      | ~ l1_pre_topc(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_828,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_819])).

tff(c_838,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_828])).

tff(c_44,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_822,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_819])).

tff(c_834,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_822])).

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

tff(c_30,plain,
    ( r1_tsep_1('#skF_4','#skF_3')
    | r1_tsep_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_56,plain,(
    r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_30])).

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
    inference(resolution,[status(thm)],[c_56,c_145])).

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

tff(c_32,plain,
    ( ~ r1_tsep_1('#skF_4','#skF_2')
    | ~ r1_tsep_1('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_57,plain,(
    ~ r1_tsep_1('#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_802,plain,
    ( ~ l1_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_797,c_57])).

tff(c_808,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_802])).

tff(c_811,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_808])).

tff(c_815,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_811])).

tff(c_816,plain,(
    ~ r1_tsep_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_817,plain,(
    r1_tsep_1('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_885,plain,(
    ! [B_163,A_164] :
      ( r1_tsep_1(B_163,A_164)
      | ~ r1_tsep_1(A_164,B_163)
      | ~ l1_struct_0(B_163)
      | ~ l1_struct_0(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_887,plain,
    ( r1_tsep_1('#skF_4','#skF_2')
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_817,c_885])).

tff(c_892,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_816,c_887])).

tff(c_896,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_892])).

tff(c_899,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_896])).

tff(c_903,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_834,c_899])).

tff(c_904,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_892])).

tff(c_908,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_904])).

tff(c_912,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_838,c_908])).

tff(c_914,plain,(
    ~ r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_913,plain,(
    r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_989,plain,(
    ! [B_178,A_179] :
      ( r1_tsep_1(B_178,A_179)
      | ~ r1_tsep_1(A_179,B_178)
      | ~ l1_struct_0(B_178)
      | ~ l1_struct_0(A_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_991,plain,
    ( r1_tsep_1('#skF_3','#skF_4')
    | ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_913,c_989])).

tff(c_994,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_914,c_991])).

tff(c_995,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_994])).

tff(c_1000,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_995])).

tff(c_1004,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_935,c_1000])).

tff(c_1005,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_994])).

tff(c_1009,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_1005])).

tff(c_1013,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_943,c_1009])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:51:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.50/1.82  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.50/1.83  
% 3.50/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.50/1.83  %$ r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k4_xboole_0 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.50/1.83  
% 3.50/1.83  %Foreground sorts:
% 3.50/1.83  
% 3.50/1.83  
% 3.50/1.83  %Background operators:
% 3.50/1.83  
% 3.50/1.83  
% 3.50/1.83  %Foreground operators:
% 3.50/1.83  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.50/1.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.50/1.83  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.50/1.83  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.50/1.83  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.50/1.83  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.50/1.83  tff('#skF_2', type, '#skF_2': $i).
% 3.50/1.83  tff('#skF_3', type, '#skF_3': $i).
% 3.50/1.83  tff('#skF_1', type, '#skF_1': $i).
% 3.50/1.83  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.50/1.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.50/1.83  tff('#skF_4', type, '#skF_4': $i).
% 3.50/1.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.50/1.83  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.50/1.83  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.50/1.83  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 3.50/1.83  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.50/1.83  
% 3.58/1.85  tff(f_128, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (m1_pre_topc(B, C) => ((r1_tsep_1(B, D) & r1_tsep_1(D, B)) | (~r1_tsep_1(C, D) & ~r1_tsep_1(D, C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_tmap_1)).
% 3.58/1.85  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.58/1.85  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.58/1.85  tff(f_76, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 3.58/1.85  tff(f_48, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.58/1.85  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.58/1.85  tff(f_90, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 3.58/1.85  tff(f_68, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tsep_1)).
% 3.58/1.85  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.58/1.85  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 3.58/1.85  tff(c_48, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.58/1.85  tff(c_40, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.58/1.85  tff(c_916, plain, (![B_165, A_166]: (l1_pre_topc(B_165) | ~m1_pre_topc(B_165, A_166) | ~l1_pre_topc(A_166))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.58/1.85  tff(c_928, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_916])).
% 3.58/1.85  tff(c_938, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_928])).
% 3.58/1.85  tff(c_34, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.58/1.85  tff(c_932, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_916])).
% 3.58/1.85  tff(c_939, plain, (~l1_pre_topc('#skF_3')), inference(splitLeft, [status(thm)], [c_932])).
% 3.58/1.85  tff(c_941, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_938, c_939])).
% 3.58/1.85  tff(c_943, plain, (l1_pre_topc('#skF_3')), inference(splitRight, [status(thm)], [c_932])).
% 3.58/1.85  tff(c_16, plain, (![A_11]: (l1_struct_0(A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.58/1.85  tff(c_36, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.58/1.85  tff(c_925, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_916])).
% 3.58/1.85  tff(c_935, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_925])).
% 3.58/1.85  tff(c_819, plain, (![B_152, A_153]: (l1_pre_topc(B_152) | ~m1_pre_topc(B_152, A_153) | ~l1_pre_topc(A_153))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.58/1.85  tff(c_828, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_819])).
% 3.58/1.85  tff(c_838, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_828])).
% 3.58/1.85  tff(c_44, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.58/1.85  tff(c_822, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_819])).
% 3.58/1.85  tff(c_834, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_822])).
% 3.58/1.85  tff(c_59, plain, (![B_42, A_43]: (l1_pre_topc(B_42) | ~m1_pre_topc(B_42, A_43) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.58/1.85  tff(c_62, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_59])).
% 3.58/1.85  tff(c_74, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_62])).
% 3.58/1.85  tff(c_68, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_59])).
% 3.58/1.85  tff(c_78, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_68])).
% 3.58/1.85  tff(c_71, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_59])).
% 3.58/1.85  tff(c_81, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_71])).
% 3.58/1.85  tff(c_30, plain, (r1_tsep_1('#skF_4', '#skF_3') | r1_tsep_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.58/1.85  tff(c_56, plain, (r1_tsep_1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_30])).
% 3.58/1.85  tff(c_145, plain, (![B_56, A_57]: (r1_tsep_1(B_56, A_57) | ~r1_tsep_1(A_57, B_56) | ~l1_struct_0(B_56) | ~l1_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.58/1.85  tff(c_148, plain, (r1_tsep_1('#skF_4', '#skF_3') | ~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_56, c_145])).
% 3.58/1.85  tff(c_149, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_148])).
% 3.58/1.85  tff(c_152, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_16, c_149])).
% 3.58/1.85  tff(c_156, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_81, c_152])).
% 3.58/1.85  tff(c_157, plain, (~l1_struct_0('#skF_4') | r1_tsep_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_148])).
% 3.58/1.85  tff(c_164, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_157])).
% 3.58/1.85  tff(c_167, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_16, c_164])).
% 3.58/1.85  tff(c_171, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_167])).
% 3.58/1.85  tff(c_173, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_157])).
% 3.58/1.85  tff(c_172, plain, (r1_tsep_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_157])).
% 3.58/1.85  tff(c_158, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_148])).
% 3.58/1.85  tff(c_50, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.58/1.85  tff(c_100, plain, (![B_51, A_52]: (v2_pre_topc(B_51) | ~m1_pre_topc(B_51, A_52) | ~l1_pre_topc(A_52) | ~v2_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.58/1.85  tff(c_112, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_100])).
% 3.58/1.85  tff(c_124, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_112])).
% 3.58/1.85  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.58/1.85  tff(c_345, plain, (![B_99, C_100, A_101]: (m1_pre_topc(B_99, C_100) | ~r1_tarski(u1_struct_0(B_99), u1_struct_0(C_100)) | ~m1_pre_topc(C_100, A_101) | ~m1_pre_topc(B_99, A_101) | ~l1_pre_topc(A_101) | ~v2_pre_topc(A_101))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.58/1.85  tff(c_362, plain, (![B_102, A_103]: (m1_pre_topc(B_102, B_102) | ~m1_pre_topc(B_102, A_103) | ~l1_pre_topc(A_103) | ~v2_pre_topc(A_103))), inference(resolution, [status(thm)], [c_6, c_345])).
% 3.58/1.85  tff(c_370, plain, (m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_362])).
% 3.58/1.85  tff(c_382, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_370])).
% 3.58/1.85  tff(c_26, plain, (![B_24, C_26, A_20]: (r1_tarski(u1_struct_0(B_24), u1_struct_0(C_26)) | ~m1_pre_topc(B_24, C_26) | ~m1_pre_topc(C_26, A_20) | ~m1_pre_topc(B_24, A_20) | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.58/1.85  tff(c_431, plain, (![B_24]: (r1_tarski(u1_struct_0(B_24), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_24, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_382, c_26])).
% 3.58/1.85  tff(c_443, plain, (![B_24]: (r1_tarski(u1_struct_0(B_24), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_24, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_81, c_431])).
% 3.58/1.85  tff(c_159, plain, (![A_58, B_59]: (r1_xboole_0(u1_struct_0(A_58), u1_struct_0(B_59)) | ~r1_tsep_1(A_58, B_59) | ~l1_struct_0(B_59) | ~l1_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.58/1.85  tff(c_8, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=A_3 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.58/1.85  tff(c_618, plain, (![A_113, B_114]: (k4_xboole_0(u1_struct_0(A_113), u1_struct_0(B_114))=u1_struct_0(A_113) | ~r1_tsep_1(A_113, B_114) | ~l1_struct_0(B_114) | ~l1_struct_0(A_113))), inference(resolution, [status(thm)], [c_159, c_8])).
% 3.58/1.85  tff(c_12, plain, (![A_5, C_7, B_6]: (r1_xboole_0(A_5, k4_xboole_0(C_7, B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.58/1.85  tff(c_746, plain, (![A_138, A_139, B_140]: (r1_xboole_0(A_138, u1_struct_0(A_139)) | ~r1_tarski(A_138, u1_struct_0(B_140)) | ~r1_tsep_1(A_139, B_140) | ~l1_struct_0(B_140) | ~l1_struct_0(A_139))), inference(superposition, [status(thm), theory('equality')], [c_618, c_12])).
% 3.58/1.85  tff(c_748, plain, (![B_24, A_139]: (r1_xboole_0(u1_struct_0(B_24), u1_struct_0(A_139)) | ~r1_tsep_1(A_139, '#skF_3') | ~l1_struct_0('#skF_3') | ~l1_struct_0(A_139) | ~m1_pre_topc(B_24, '#skF_3'))), inference(resolution, [status(thm)], [c_443, c_746])).
% 3.58/1.85  tff(c_773, plain, (![B_143, A_144]: (r1_xboole_0(u1_struct_0(B_143), u1_struct_0(A_144)) | ~r1_tsep_1(A_144, '#skF_3') | ~l1_struct_0(A_144) | ~m1_pre_topc(B_143, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_748])).
% 3.58/1.85  tff(c_20, plain, (![A_15, B_17]: (r1_tsep_1(A_15, B_17) | ~r1_xboole_0(u1_struct_0(A_15), u1_struct_0(B_17)) | ~l1_struct_0(B_17) | ~l1_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.58/1.85  tff(c_791, plain, (![B_147, A_148]: (r1_tsep_1(B_147, A_148) | ~l1_struct_0(B_147) | ~r1_tsep_1(A_148, '#skF_3') | ~l1_struct_0(A_148) | ~m1_pre_topc(B_147, '#skF_3'))), inference(resolution, [status(thm)], [c_773, c_20])).
% 3.58/1.85  tff(c_793, plain, (![B_147]: (r1_tsep_1(B_147, '#skF_4') | ~l1_struct_0(B_147) | ~l1_struct_0('#skF_4') | ~m1_pre_topc(B_147, '#skF_3'))), inference(resolution, [status(thm)], [c_172, c_791])).
% 3.58/1.85  tff(c_797, plain, (![B_149]: (r1_tsep_1(B_149, '#skF_4') | ~l1_struct_0(B_149) | ~m1_pre_topc(B_149, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_793])).
% 3.58/1.85  tff(c_32, plain, (~r1_tsep_1('#skF_4', '#skF_2') | ~r1_tsep_1('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.58/1.85  tff(c_57, plain, (~r1_tsep_1('#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_32])).
% 3.58/1.85  tff(c_802, plain, (~l1_struct_0('#skF_2') | ~m1_pre_topc('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_797, c_57])).
% 3.58/1.85  tff(c_808, plain, (~l1_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_802])).
% 3.58/1.85  tff(c_811, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_16, c_808])).
% 3.58/1.85  tff(c_815, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_811])).
% 3.58/1.85  tff(c_816, plain, (~r1_tsep_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_32])).
% 3.58/1.85  tff(c_817, plain, (r1_tsep_1('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_32])).
% 3.58/1.85  tff(c_885, plain, (![B_163, A_164]: (r1_tsep_1(B_163, A_164) | ~r1_tsep_1(A_164, B_163) | ~l1_struct_0(B_163) | ~l1_struct_0(A_164))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.58/1.85  tff(c_887, plain, (r1_tsep_1('#skF_4', '#skF_2') | ~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_817, c_885])).
% 3.58/1.85  tff(c_892, plain, (~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_816, c_887])).
% 3.58/1.85  tff(c_896, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_892])).
% 3.58/1.85  tff(c_899, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_16, c_896])).
% 3.58/1.85  tff(c_903, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_834, c_899])).
% 3.58/1.85  tff(c_904, plain, (~l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_892])).
% 3.58/1.85  tff(c_908, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_16, c_904])).
% 3.58/1.85  tff(c_912, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_838, c_908])).
% 3.58/1.85  tff(c_914, plain, (~r1_tsep_1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_30])).
% 3.58/1.85  tff(c_913, plain, (r1_tsep_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_30])).
% 3.58/1.85  tff(c_989, plain, (![B_178, A_179]: (r1_tsep_1(B_178, A_179) | ~r1_tsep_1(A_179, B_178) | ~l1_struct_0(B_178) | ~l1_struct_0(A_179))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.58/1.85  tff(c_991, plain, (r1_tsep_1('#skF_3', '#skF_4') | ~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_913, c_989])).
% 3.58/1.85  tff(c_994, plain, (~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_914, c_991])).
% 3.58/1.85  tff(c_995, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_994])).
% 3.58/1.85  tff(c_1000, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_16, c_995])).
% 3.58/1.85  tff(c_1004, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_935, c_1000])).
% 3.58/1.85  tff(c_1005, plain, (~l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_994])).
% 3.58/1.85  tff(c_1009, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_16, c_1005])).
% 3.58/1.85  tff(c_1013, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_943, c_1009])).
% 3.58/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/1.85  
% 3.58/1.85  Inference rules
% 3.58/1.85  ----------------------
% 3.58/1.85  #Ref     : 0
% 3.58/1.85  #Sup     : 200
% 3.58/1.85  #Fact    : 0
% 3.58/1.85  #Define  : 0
% 3.58/1.85  #Split   : 11
% 3.58/1.85  #Chain   : 0
% 3.58/1.85  #Close   : 0
% 3.58/1.85  
% 3.58/1.85  Ordering : KBO
% 3.58/1.85  
% 3.58/1.85  Simplification rules
% 3.58/1.85  ----------------------
% 3.58/1.85  #Subsume      : 21
% 3.58/1.85  #Demod        : 122
% 3.58/1.85  #Tautology    : 50
% 3.58/1.85  #SimpNegUnit  : 2
% 3.58/1.85  #BackRed      : 0
% 3.58/1.85  
% 3.58/1.85  #Partial instantiations: 0
% 3.58/1.85  #Strategies tried      : 1
% 3.58/1.85  
% 3.58/1.85  Timing (in seconds)
% 3.58/1.85  ----------------------
% 3.58/1.86  Preprocessing        : 0.47
% 3.58/1.86  Parsing              : 0.25
% 3.58/1.86  CNF conversion       : 0.04
% 3.58/1.86  Main loop            : 0.50
% 3.58/1.86  Inferencing          : 0.18
% 3.58/1.86  Reduction            : 0.13
% 3.58/1.86  Demodulation         : 0.09
% 3.58/1.86  BG Simplification    : 0.03
% 3.58/1.86  Subsumption          : 0.10
% 3.58/1.86  Abstraction          : 0.02
% 3.58/1.86  MUC search           : 0.00
% 3.58/1.86  Cooper               : 0.00
% 3.58/1.86  Total                : 1.01
% 3.58/1.86  Index Insertion      : 0.00
% 3.58/1.86  Index Deletion       : 0.00
% 3.58/1.86  Index Matching       : 0.00
% 3.58/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
