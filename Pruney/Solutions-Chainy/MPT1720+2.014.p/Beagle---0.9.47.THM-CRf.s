%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:43 EST 2020

% Result     : Theorem 11.05s
% Output     : CNFRefutation 11.14s
% Verified   : 
% Statistics : Number of formulae       :  148 (5893 expanded)
%              Number of leaves         :   26 (2257 expanded)
%              Depth                    :   33
%              Number of atoms          :  569 (35774 expanded)
%              Number of equality atoms :   48 (1732 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k1_tsep_1 > k2_xboole_0 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_tsep_1,type,(
    k1_tsep_1: ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(f_170,negated_conjecture,(
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
                   => ( ( m1_pre_topc(B,C)
                        & m1_pre_topc(D,C) )
                     => m1_pre_topc(k1_tsep_1(A,B,D),C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tmap_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & m1_pre_topc(B,A)
        & ~ v2_struct_0(C)
        & m1_pre_topc(C,A) )
     => ( ~ v2_struct_0(k1_tsep_1(A,B,C))
        & v1_pre_topc(k1_tsep_1(A,B,C))
        & m1_pre_topc(k1_tsep_1(A,B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).

tff(f_124,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => k1_tsep_1(A,B,B) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tmap_1)).

tff(f_109,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( m1_pre_topc(B,C)
              <=> k1_tsep_1(A,B,C) = g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tsep_1)).

tff(f_138,axiom,(
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

tff(f_64,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & v1_pre_topc(D)
                    & m1_pre_topc(D,A) )
                 => ( D = k1_tsep_1(A,B,C)
                  <=> u1_struct_0(D) = k2_xboole_0(u1_struct_0(B),u1_struct_0(C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tsep_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_xboole_1)).

tff(c_46,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_44,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_36,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_40,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_32,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_10,plain,(
    ! [A_22,B_23,C_24] :
      ( m1_pre_topc(k1_tsep_1(A_22,B_23,C_24),A_22)
      | ~ m1_pre_topc(C_24,A_22)
      | v2_struct_0(C_24)
      | ~ m1_pre_topc(B_23,A_22)
      | v2_struct_0(B_23)
      | ~ l1_pre_topc(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_195,plain,(
    ! [A_81,B_82] :
      ( k1_tsep_1(A_81,B_82,B_82) = g1_pre_topc(u1_struct_0(B_82),u1_pre_topc(B_82))
      | ~ m1_pre_topc(B_82,A_81)
      | v2_struct_0(B_82)
      | ~ l1_pre_topc(A_81)
      | ~ v2_pre_topc(A_81)
      | v2_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_205,plain,
    ( g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = k1_tsep_1('#skF_1','#skF_3','#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_195])).

tff(c_220,plain,
    ( g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = k1_tsep_1('#skF_1','#skF_3','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_205])).

tff(c_221,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = k1_tsep_1('#skF_1','#skF_3','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_38,c_220])).

tff(c_28,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_1210,plain,(
    ! [A_153,B_154,C_155] :
      ( k1_tsep_1(A_153,B_154,C_155) = g1_pre_topc(u1_struct_0(C_155),u1_pre_topc(C_155))
      | ~ m1_pre_topc(B_154,C_155)
      | ~ m1_pre_topc(C_155,A_153)
      | v2_struct_0(C_155)
      | ~ m1_pre_topc(B_154,A_153)
      | v2_struct_0(B_154)
      | ~ l1_pre_topc(A_153)
      | ~ v2_pre_topc(A_153)
      | v2_struct_0(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1214,plain,(
    ! [A_153] :
      ( k1_tsep_1(A_153,'#skF_4','#skF_3') = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_153)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_4',A_153)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_153)
      | ~ v2_pre_topc(A_153)
      | v2_struct_0(A_153) ) ),
    inference(resolution,[status(thm)],[c_28,c_1210])).

tff(c_1225,plain,(
    ! [A_153] :
      ( k1_tsep_1(A_153,'#skF_4','#skF_3') = k1_tsep_1('#skF_1','#skF_3','#skF_3')
      | ~ m1_pre_topc('#skF_3',A_153)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_4',A_153)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_153)
      | ~ v2_pre_topc(A_153)
      | v2_struct_0(A_153) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_1214])).

tff(c_1292,plain,(
    ! [A_157] :
      ( k1_tsep_1(A_157,'#skF_4','#skF_3') = k1_tsep_1('#skF_1','#skF_3','#skF_3')
      | ~ m1_pre_topc('#skF_3',A_157)
      | ~ m1_pre_topc('#skF_4',A_157)
      | ~ l1_pre_topc(A_157)
      | ~ v2_pre_topc(A_157)
      | v2_struct_0(A_157) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_38,c_1225])).

tff(c_1295,plain,
    ( k1_tsep_1('#skF_1','#skF_3','#skF_3') = k1_tsep_1('#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_1292])).

tff(c_1298,plain,
    ( k1_tsep_1('#skF_1','#skF_3','#skF_3') = k1_tsep_1('#skF_1','#skF_4','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_32,c_1295])).

tff(c_1299,plain,(
    k1_tsep_1('#skF_1','#skF_3','#skF_3') = k1_tsep_1('#skF_1','#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1298])).

tff(c_1301,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = k1_tsep_1('#skF_1','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1299,c_221])).

tff(c_1369,plain,(
    ! [B_160,C_161,A_162] :
      ( m1_pre_topc(B_160,C_161)
      | k1_tsep_1(A_162,B_160,C_161) != g1_pre_topc(u1_struct_0(C_161),u1_pre_topc(C_161))
      | ~ m1_pre_topc(C_161,A_162)
      | v2_struct_0(C_161)
      | ~ m1_pre_topc(B_160,A_162)
      | v2_struct_0(B_160)
      | ~ l1_pre_topc(A_162)
      | ~ v2_pre_topc(A_162)
      | v2_struct_0(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1371,plain,(
    ! [B_160,A_162] :
      ( m1_pre_topc(B_160,'#skF_3')
      | k1_tsep_1(A_162,B_160,'#skF_3') != k1_tsep_1('#skF_1','#skF_4','#skF_3')
      | ~ m1_pre_topc('#skF_3',A_162)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_160,A_162)
      | v2_struct_0(B_160)
      | ~ l1_pre_topc(A_162)
      | ~ v2_pre_topc(A_162)
      | v2_struct_0(A_162) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1301,c_1369])).

tff(c_16269,plain,(
    ! [B_545,A_546] :
      ( m1_pre_topc(B_545,'#skF_3')
      | k1_tsep_1(A_546,B_545,'#skF_3') != k1_tsep_1('#skF_1','#skF_4','#skF_3')
      | ~ m1_pre_topc('#skF_3',A_546)
      | ~ m1_pre_topc(B_545,A_546)
      | v2_struct_0(B_545)
      | ~ l1_pre_topc(A_546)
      | ~ v2_pre_topc(A_546)
      | v2_struct_0(A_546) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1371])).

tff(c_16276,plain,(
    ! [B_545] :
      ( m1_pre_topc(B_545,'#skF_3')
      | k1_tsep_1('#skF_1',B_545,'#skF_3') != k1_tsep_1('#skF_1','#skF_4','#skF_3')
      | ~ m1_pre_topc(B_545,'#skF_1')
      | v2_struct_0(B_545)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_36,c_16269])).

tff(c_16285,plain,(
    ! [B_545] :
      ( m1_pre_topc(B_545,'#skF_3')
      | k1_tsep_1('#skF_1',B_545,'#skF_3') != k1_tsep_1('#skF_1','#skF_4','#skF_3')
      | ~ m1_pre_topc(B_545,'#skF_1')
      | v2_struct_0(B_545)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_16276])).

tff(c_16287,plain,(
    ! [B_547] :
      ( m1_pre_topc(B_547,'#skF_3')
      | k1_tsep_1('#skF_1',B_547,'#skF_3') != k1_tsep_1('#skF_1','#skF_4','#skF_3')
      | ~ m1_pre_topc(B_547,'#skF_1')
      | v2_struct_0(B_547) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_16285])).

tff(c_26,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_16397,plain,
    ( k1_tsep_1('#skF_1',k1_tsep_1('#skF_1','#skF_2','#skF_4'),'#skF_3') != k1_tsep_1('#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_4'),'#skF_1')
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_16287,c_26])).

tff(c_16883,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_4'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_16397])).

tff(c_16886,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_16883])).

tff(c_16889,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_32,c_16886])).

tff(c_16891,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_42,c_34,c_16889])).

tff(c_16893,plain,(
    m1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_4'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_16397])).

tff(c_83,plain,(
    ! [B_66,C_67,A_68] :
      ( r1_tarski(u1_struct_0(B_66),u1_struct_0(C_67))
      | ~ m1_pre_topc(B_66,C_67)
      | ~ m1_pre_topc(C_67,A_68)
      | ~ m1_pre_topc(B_66,A_68)
      | ~ l1_pre_topc(A_68)
      | ~ v2_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_93,plain,(
    ! [B_66] :
      ( r1_tarski(u1_struct_0(B_66),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_66,'#skF_3')
      | ~ m1_pre_topc(B_66,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_36,c_83])).

tff(c_104,plain,(
    ! [B_66] :
      ( r1_tarski(u1_struct_0(B_66),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_66,'#skF_3')
      | ~ m1_pre_topc(B_66,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_93])).

tff(c_30,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_12,plain,(
    ! [A_22,B_23,C_24] :
      ( v1_pre_topc(k1_tsep_1(A_22,B_23,C_24))
      | ~ m1_pre_topc(C_24,A_22)
      | v2_struct_0(C_24)
      | ~ m1_pre_topc(B_23,A_22)
      | v2_struct_0(B_23)
      | ~ l1_pre_topc(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_6217,plain,(
    ! [A_314,B_315,C_316] :
      ( u1_struct_0(k1_tsep_1(A_314,B_315,C_316)) = k2_xboole_0(u1_struct_0(B_315),u1_struct_0(C_316))
      | ~ m1_pre_topc(k1_tsep_1(A_314,B_315,C_316),A_314)
      | ~ v1_pre_topc(k1_tsep_1(A_314,B_315,C_316))
      | v2_struct_0(k1_tsep_1(A_314,B_315,C_316))
      | ~ m1_pre_topc(C_316,A_314)
      | v2_struct_0(C_316)
      | ~ m1_pre_topc(B_315,A_314)
      | v2_struct_0(B_315)
      | ~ l1_pre_topc(A_314)
      | v2_struct_0(A_314) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6850,plain,(
    ! [A_328,B_329,C_330] :
      ( u1_struct_0(k1_tsep_1(A_328,B_329,C_330)) = k2_xboole_0(u1_struct_0(B_329),u1_struct_0(C_330))
      | ~ v1_pre_topc(k1_tsep_1(A_328,B_329,C_330))
      | v2_struct_0(k1_tsep_1(A_328,B_329,C_330))
      | ~ m1_pre_topc(C_330,A_328)
      | v2_struct_0(C_330)
      | ~ m1_pre_topc(B_329,A_328)
      | v2_struct_0(B_329)
      | ~ l1_pre_topc(A_328)
      | v2_struct_0(A_328) ) ),
    inference(resolution,[status(thm)],[c_10,c_6217])).

tff(c_87,plain,(
    ! [B_66] :
      ( r1_tarski(u1_struct_0(B_66),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_66,'#skF_4')
      | ~ m1_pre_topc(B_66,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_32,c_83])).

tff(c_97,plain,(
    ! [B_66] :
      ( r1_tarski(u1_struct_0(B_66),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_66,'#skF_4')
      | ~ m1_pre_topc(B_66,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_87])).

tff(c_18714,plain,(
    ! [B_597,C_598,A_599] :
      ( r1_tarski(k2_xboole_0(u1_struct_0(B_597),u1_struct_0(C_598)),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(k1_tsep_1(A_599,B_597,C_598),'#skF_4')
      | ~ m1_pre_topc(k1_tsep_1(A_599,B_597,C_598),'#skF_1')
      | ~ v1_pre_topc(k1_tsep_1(A_599,B_597,C_598))
      | v2_struct_0(k1_tsep_1(A_599,B_597,C_598))
      | ~ m1_pre_topc(C_598,A_599)
      | v2_struct_0(C_598)
      | ~ m1_pre_topc(B_597,A_599)
      | v2_struct_0(B_597)
      | ~ l1_pre_topc(A_599)
      | v2_struct_0(A_599) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6850,c_97])).

tff(c_18716,plain,
    ( r1_tarski(k2_xboole_0(u1_struct_0('#skF_2'),u1_struct_0('#skF_4')),u1_struct_0('#skF_4'))
    | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_4'),'#skF_4')
    | ~ v1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_4'))
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_16893,c_18714])).

tff(c_18732,plain,
    ( r1_tarski(k2_xboole_0(u1_struct_0('#skF_2'),u1_struct_0('#skF_4')),u1_struct_0('#skF_4'))
    | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_4'),'#skF_4')
    | ~ v1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_4'))
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_4'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_32,c_18716])).

tff(c_18733,plain,
    ( r1_tarski(k2_xboole_0(u1_struct_0('#skF_2'),u1_struct_0('#skF_4')),u1_struct_0('#skF_4'))
    | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_4'),'#skF_4')
    | ~ v1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_4'))
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_42,c_34,c_18732])).

tff(c_19359,plain,(
    ~ v1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_18733])).

tff(c_19362,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_19359])).

tff(c_19365,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_32,c_19362])).

tff(c_19367,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_42,c_34,c_19365])).

tff(c_19369,plain,(
    v1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_18733])).

tff(c_14,plain,(
    ! [A_22,B_23,C_24] :
      ( ~ v2_struct_0(k1_tsep_1(A_22,B_23,C_24))
      | ~ m1_pre_topc(C_24,A_22)
      | v2_struct_0(C_24)
      | ~ m1_pre_topc(B_23,A_22)
      | v2_struct_0(B_23)
      | ~ l1_pre_topc(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_7066,plain,(
    ! [A_328,B_329,C_330] :
      ( u1_struct_0(k1_tsep_1(A_328,B_329,C_330)) = k2_xboole_0(u1_struct_0(B_329),u1_struct_0(C_330))
      | ~ v1_pre_topc(k1_tsep_1(A_328,B_329,C_330))
      | ~ m1_pre_topc(C_330,A_328)
      | v2_struct_0(C_330)
      | ~ m1_pre_topc(B_329,A_328)
      | v2_struct_0(B_329)
      | ~ l1_pre_topc(A_328)
      | v2_struct_0(A_328) ) ),
    inference(resolution,[status(thm)],[c_6850,c_14])).

tff(c_19371,plain,
    ( k2_xboole_0(u1_struct_0('#skF_2'),u1_struct_0('#skF_4')) = u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_19369,c_7066])).

tff(c_19374,plain,
    ( k2_xboole_0(u1_struct_0('#skF_2'),u1_struct_0('#skF_4')) = u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_4'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_32,c_19371])).

tff(c_19375,plain,(
    k2_xboole_0(u1_struct_0('#skF_2'),u1_struct_0('#skF_4')) = u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_42,c_34,c_19374])).

tff(c_1308,plain,
    ( ~ v2_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1299,c_14])).

tff(c_1318,plain,
    ( ~ v2_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_36,c_36,c_1308])).

tff(c_1319,plain,(
    ~ v2_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_38,c_1318])).

tff(c_1305,plain,
    ( m1_pre_topc(k1_tsep_1('#skF_1','#skF_4','#skF_3'),'#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1299,c_10])).

tff(c_1315,plain,
    ( m1_pre_topc(k1_tsep_1('#skF_1','#skF_4','#skF_3'),'#skF_1')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_36,c_36,c_1305])).

tff(c_1316,plain,(
    m1_pre_topc(k1_tsep_1('#skF_1','#skF_4','#skF_3'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_38,c_1315])).

tff(c_234,plain,(
    ! [A_83,B_84,C_85] :
      ( m1_pre_topc(k1_tsep_1(A_83,B_84,C_85),A_83)
      | ~ m1_pre_topc(C_85,A_83)
      | v2_struct_0(C_85)
      | ~ m1_pre_topc(B_84,A_83)
      | v2_struct_0(B_84)
      | ~ l1_pre_topc(A_83)
      | v2_struct_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_20,plain,(
    ! [A_32,B_34] :
      ( k1_tsep_1(A_32,B_34,B_34) = g1_pre_topc(u1_struct_0(B_34),u1_pre_topc(B_34))
      | ~ m1_pre_topc(B_34,A_32)
      | v2_struct_0(B_34)
      | ~ l1_pre_topc(A_32)
      | ~ v2_pre_topc(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_7310,plain,(
    ! [A_339,B_340,C_341] :
      ( k1_tsep_1(A_339,k1_tsep_1(A_339,B_340,C_341),k1_tsep_1(A_339,B_340,C_341)) = g1_pre_topc(u1_struct_0(k1_tsep_1(A_339,B_340,C_341)),u1_pre_topc(k1_tsep_1(A_339,B_340,C_341)))
      | v2_struct_0(k1_tsep_1(A_339,B_340,C_341))
      | ~ v2_pre_topc(A_339)
      | ~ m1_pre_topc(C_341,A_339)
      | v2_struct_0(C_341)
      | ~ m1_pre_topc(B_340,A_339)
      | v2_struct_0(B_340)
      | ~ l1_pre_topc(A_339)
      | v2_struct_0(A_339) ) ),
    inference(resolution,[status(thm)],[c_234,c_20])).

tff(c_16,plain,(
    ! [B_29,C_31,A_25] :
      ( m1_pre_topc(B_29,C_31)
      | k1_tsep_1(A_25,B_29,C_31) != g1_pre_topc(u1_struct_0(C_31),u1_pre_topc(C_31))
      | ~ m1_pre_topc(C_31,A_25)
      | v2_struct_0(C_31)
      | ~ m1_pre_topc(B_29,A_25)
      | v2_struct_0(B_29)
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_10268,plain,(
    ! [A_419,B_420,C_421] :
      ( m1_pre_topc(k1_tsep_1(A_419,B_420,C_421),k1_tsep_1(A_419,B_420,C_421))
      | ~ m1_pre_topc(k1_tsep_1(A_419,B_420,C_421),A_419)
      | v2_struct_0(k1_tsep_1(A_419,B_420,C_421))
      | ~ v2_pre_topc(A_419)
      | ~ m1_pre_topc(C_421,A_419)
      | v2_struct_0(C_421)
      | ~ m1_pre_topc(B_420,A_419)
      | v2_struct_0(B_420)
      | ~ l1_pre_topc(A_419)
      | v2_struct_0(A_419) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7310,c_16])).

tff(c_1220,plain,(
    ! [A_153] :
      ( k1_tsep_1(A_153,'#skF_2','#skF_3') = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_153)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_2',A_153)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_153)
      | ~ v2_pre_topc(A_153)
      | v2_struct_0(A_153) ) ),
    inference(resolution,[status(thm)],[c_30,c_1210])).

tff(c_1234,plain,(
    ! [A_153] :
      ( k1_tsep_1(A_153,'#skF_2','#skF_3') = k1_tsep_1('#skF_1','#skF_3','#skF_3')
      | ~ m1_pre_topc('#skF_3',A_153)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_2',A_153)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_153)
      | ~ v2_pre_topc(A_153)
      | v2_struct_0(A_153) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_1220])).

tff(c_1235,plain,(
    ! [A_153] :
      ( k1_tsep_1(A_153,'#skF_2','#skF_3') = k1_tsep_1('#skF_1','#skF_3','#skF_3')
      | ~ m1_pre_topc('#skF_3',A_153)
      | ~ m1_pre_topc('#skF_2',A_153)
      | ~ l1_pre_topc(A_153)
      | ~ v2_pre_topc(A_153)
      | v2_struct_0(A_153) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_38,c_1234])).

tff(c_1356,plain,(
    ! [A_159] :
      ( k1_tsep_1(A_159,'#skF_2','#skF_3') = k1_tsep_1('#skF_1','#skF_4','#skF_3')
      | ~ m1_pre_topc('#skF_3',A_159)
      | ~ m1_pre_topc('#skF_2',A_159)
      | ~ l1_pre_topc(A_159)
      | ~ v2_pre_topc(A_159)
      | v2_struct_0(A_159) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1299,c_1235])).

tff(c_1359,plain,
    ( k1_tsep_1('#skF_1','#skF_2','#skF_3') = k1_tsep_1('#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_1356])).

tff(c_1365,plain,
    ( k1_tsep_1('#skF_1','#skF_2','#skF_3') = k1_tsep_1('#skF_1','#skF_4','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_36,c_1359])).

tff(c_1366,plain,(
    k1_tsep_1('#skF_1','#skF_2','#skF_3') = k1_tsep_1('#skF_1','#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1365])).

tff(c_1311,plain,
    ( v1_pre_topc(k1_tsep_1('#skF_1','#skF_4','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1299,c_12])).

tff(c_1321,plain,
    ( v1_pre_topc(k1_tsep_1('#skF_1','#skF_4','#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_36,c_36,c_1311])).

tff(c_1322,plain,(
    v1_pre_topc(k1_tsep_1('#skF_1','#skF_4','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_38,c_1321])).

tff(c_6219,plain,
    ( k2_xboole_0(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) = u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_4','#skF_3'),'#skF_1')
    | ~ v1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1366,c_6217])).

tff(c_6227,plain,
    ( k2_xboole_0(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) = u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_3'))
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_36,c_1366,c_1322,c_1366,c_1316,c_1366,c_6219])).

tff(c_6228,plain,(
    k2_xboole_0(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) = u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_42,c_38,c_1319,c_6227])).

tff(c_122,plain,(
    ! [B_71] :
      ( r1_tarski(u1_struct_0(B_71),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_71,'#skF_3')
      | ~ m1_pre_topc(B_71,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_93])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k2_xboole_0(A_1,B_2) = B_2
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_129,plain,(
    ! [B_71] :
      ( k2_xboole_0(u1_struct_0(B_71),u1_struct_0('#skF_3')) = u1_struct_0('#skF_3')
      | ~ m1_pre_topc(B_71,'#skF_3')
      | ~ m1_pre_topc(B_71,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_122,c_2])).

tff(c_6320,plain,
    ( u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_3')) = u1_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6228,c_129])).

tff(c_6349,plain,(
    u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_3')) = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_30,c_6320])).

tff(c_22,plain,(
    ! [B_39,C_41,A_35] :
      ( r1_tarski(u1_struct_0(B_39),u1_struct_0(C_41))
      | ~ m1_pre_topc(B_39,C_41)
      | ~ m1_pre_topc(C_41,A_35)
      | ~ m1_pre_topc(B_39,A_35)
      | ~ l1_pre_topc(A_35)
      | ~ v2_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_6666,plain,(
    ! [B_319,A_320,B_321,C_322] :
      ( r1_tarski(u1_struct_0(B_319),u1_struct_0(k1_tsep_1(A_320,B_321,C_322)))
      | ~ m1_pre_topc(B_319,k1_tsep_1(A_320,B_321,C_322))
      | ~ m1_pre_topc(B_319,A_320)
      | ~ v2_pre_topc(A_320)
      | ~ m1_pre_topc(C_322,A_320)
      | v2_struct_0(C_322)
      | ~ m1_pre_topc(B_321,A_320)
      | v2_struct_0(B_321)
      | ~ l1_pre_topc(A_320)
      | v2_struct_0(A_320) ) ),
    inference(resolution,[status(thm)],[c_234,c_22])).

tff(c_6690,plain,(
    ! [B_319] :
      ( r1_tarski(u1_struct_0(B_319),u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_3')))
      | ~ m1_pre_topc(B_319,k1_tsep_1('#skF_1','#skF_2','#skF_3'))
      | ~ m1_pre_topc(B_319,'#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_2','#skF_1')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1366,c_6666])).

tff(c_6705,plain,(
    ! [B_319] :
      ( r1_tarski(u1_struct_0(B_319),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_319,k1_tsep_1('#skF_1','#skF_4','#skF_3'))
      | ~ m1_pre_topc(B_319,'#skF_1')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_36,c_46,c_1366,c_6349,c_6690])).

tff(c_6711,plain,(
    ! [B_323] :
      ( r1_tarski(u1_struct_0(B_323),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_323,k1_tsep_1('#skF_1','#skF_4','#skF_3'))
      | ~ m1_pre_topc(B_323,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_42,c_38,c_6705])).

tff(c_6729,plain,
    ( r1_tarski(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))
    | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_4','#skF_3'),k1_tsep_1('#skF_1','#skF_4','#skF_3'))
    | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_4','#skF_3'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6349,c_6711])).

tff(c_6742,plain,
    ( r1_tarski(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))
    | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_4','#skF_3'),k1_tsep_1('#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1316,c_6729])).

tff(c_7135,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_4','#skF_3'),k1_tsep_1('#skF_1','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_6742])).

tff(c_10275,plain,
    ( ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_4','#skF_3'),'#skF_1')
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_3'))
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_10268,c_7135])).

tff(c_10310,plain,
    ( v2_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_32,c_36,c_46,c_1316,c_10275])).

tff(c_10312,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_34,c_38,c_1319,c_10310])).

tff(c_10313,plain,(
    r1_tarski(u1_struct_0('#skF_3'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_6742])).

tff(c_24,plain,(
    ! [B_39,C_41,A_35] :
      ( m1_pre_topc(B_39,C_41)
      | ~ r1_tarski(u1_struct_0(B_39),u1_struct_0(C_41))
      | ~ m1_pre_topc(C_41,A_35)
      | ~ m1_pre_topc(B_39,A_35)
      | ~ l1_pre_topc(A_35)
      | ~ v2_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_10345,plain,(
    ! [A_35] :
      ( m1_pre_topc('#skF_3','#skF_3')
      | ~ m1_pre_topc('#skF_3',A_35)
      | ~ l1_pre_topc(A_35)
      | ~ v2_pre_topc(A_35) ) ),
    inference(resolution,[status(thm)],[c_10313,c_24])).

tff(c_10368,plain,(
    ! [A_422] :
      ( ~ m1_pre_topc('#skF_3',A_422)
      | ~ l1_pre_topc(A_422)
      | ~ v2_pre_topc(A_422) ) ),
    inference(splitLeft,[status(thm)],[c_10345])).

tff(c_10371,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_10368])).

tff(c_10375,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_10371])).

tff(c_10376,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_10345])).

tff(c_172,plain,(
    ! [B_74] :
      ( k2_xboole_0(u1_struct_0(B_74),u1_struct_0('#skF_3')) = u1_struct_0('#skF_3')
      | ~ m1_pre_topc(B_74,'#skF_3')
      | ~ m1_pre_topc(B_74,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_122,c_2])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4,D_6] :
      ( r1_tarski(k2_xboole_0(A_3,C_5),k2_xboole_0(B_4,D_6))
      | ~ r1_tarski(C_5,D_6)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1432,plain,(
    ! [A_168,C_169,B_170] :
      ( r1_tarski(k2_xboole_0(A_168,C_169),u1_struct_0('#skF_3'))
      | ~ r1_tarski(C_169,u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_168,u1_struct_0(B_170))
      | ~ m1_pre_topc(B_170,'#skF_3')
      | ~ m1_pre_topc(B_170,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_4])).

tff(c_1436,plain,(
    ! [B_66,C_169] :
      ( r1_tarski(k2_xboole_0(u1_struct_0(B_66),C_169),u1_struct_0('#skF_3'))
      | ~ r1_tarski(C_169,u1_struct_0('#skF_3'))
      | ~ m1_pre_topc('#skF_3','#skF_3')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | ~ m1_pre_topc(B_66,'#skF_3')
      | ~ m1_pre_topc(B_66,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_104,c_1432])).

tff(c_1446,plain,(
    ! [B_66,C_169] :
      ( r1_tarski(k2_xboole_0(u1_struct_0(B_66),C_169),u1_struct_0('#skF_3'))
      | ~ r1_tarski(C_169,u1_struct_0('#skF_3'))
      | ~ m1_pre_topc('#skF_3','#skF_3')
      | ~ m1_pre_topc(B_66,'#skF_3')
      | ~ m1_pre_topc(B_66,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1436])).

tff(c_13822,plain,(
    ! [B_66,C_169] :
      ( r1_tarski(k2_xboole_0(u1_struct_0(B_66),C_169),u1_struct_0('#skF_3'))
      | ~ r1_tarski(C_169,u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_66,'#skF_3')
      | ~ m1_pre_topc(B_66,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10376,c_1446])).

tff(c_19417,plain,
    ( r1_tarski(u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_4')),u1_struct_0('#skF_3'))
    | ~ r1_tarski(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_19375,c_13822])).

tff(c_19526,plain,
    ( r1_tarski(u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_4')),u1_struct_0('#skF_3'))
    | ~ r1_tarski(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_30,c_19417])).

tff(c_19801,plain,(
    ~ r1_tarski(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_19526])).

tff(c_19807,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_104,c_19801])).

tff(c_19814,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_19807])).

tff(c_19815,plain,(
    r1_tarski(u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_4')),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_19526])).

tff(c_19872,plain,(
    ! [A_35] :
      ( m1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_4'),'#skF_3')
      | ~ m1_pre_topc('#skF_3',A_35)
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_4'),A_35)
      | ~ l1_pre_topc(A_35)
      | ~ v2_pre_topc(A_35) ) ),
    inference(resolution,[status(thm)],[c_19815,c_24])).

tff(c_20386,plain,(
    ! [A_615] :
      ( ~ m1_pre_topc('#skF_3',A_615)
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_4'),A_615)
      | ~ l1_pre_topc(A_615)
      | ~ v2_pre_topc(A_615) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_19872])).

tff(c_20389,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16893,c_20386])).

tff(c_20409,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_36,c_20389])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:36:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.05/4.04  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.05/4.06  
% 11.05/4.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.05/4.06  %$ r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k1_tsep_1 > k2_xboole_0 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 11.05/4.06  
% 11.05/4.06  %Foreground sorts:
% 11.05/4.06  
% 11.05/4.06  
% 11.05/4.06  %Background operators:
% 11.05/4.06  
% 11.05/4.06  
% 11.05/4.06  %Foreground operators:
% 11.05/4.06  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 11.05/4.06  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 11.05/4.06  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 11.05/4.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.05/4.06  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 11.05/4.06  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 11.05/4.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.05/4.06  tff('#skF_2', type, '#skF_2': $i).
% 11.05/4.06  tff('#skF_3', type, '#skF_3': $i).
% 11.05/4.06  tff('#skF_1', type, '#skF_1': $i).
% 11.05/4.06  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 11.05/4.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.05/4.06  tff('#skF_4', type, '#skF_4': $i).
% 11.05/4.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.05/4.06  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 11.05/4.06  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 11.05/4.06  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.05/4.06  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.05/4.06  
% 11.14/4.08  tff(f_170, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => ((m1_pre_topc(B, C) & m1_pre_topc(D, C)) => m1_pre_topc(k1_tsep_1(A, B, D), C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tmap_1)).
% 11.14/4.08  tff(f_86, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => ((~v2_struct_0(k1_tsep_1(A, B, C)) & v1_pre_topc(k1_tsep_1(A, B, C))) & m1_pre_topc(k1_tsep_1(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 11.14/4.08  tff(f_124, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (k1_tsep_1(A, B, B) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_tmap_1)).
% 11.14/4.08  tff(f_109, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (m1_pre_topc(B, C) <=> (k1_tsep_1(A, B, C) = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_tsep_1)).
% 11.14/4.08  tff(f_138, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 11.14/4.08  tff(f_64, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (((~v2_struct_0(D) & v1_pre_topc(D)) & m1_pre_topc(D, A)) => ((D = k1_tsep_1(A, B, C)) <=> (u1_struct_0(D) = k2_xboole_0(u1_struct_0(B), u1_struct_0(C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tsep_1)).
% 11.14/4.08  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 11.14/4.08  tff(f_35, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_xboole_1)).
% 11.14/4.08  tff(c_46, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_170])).
% 11.14/4.08  tff(c_44, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_170])).
% 11.14/4.08  tff(c_36, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_170])).
% 11.14/4.08  tff(c_48, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_170])).
% 11.14/4.08  tff(c_42, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_170])).
% 11.14/4.08  tff(c_34, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_170])).
% 11.14/4.08  tff(c_40, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_170])).
% 11.14/4.08  tff(c_32, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_170])).
% 11.14/4.08  tff(c_10, plain, (![A_22, B_23, C_24]: (m1_pre_topc(k1_tsep_1(A_22, B_23, C_24), A_22) | ~m1_pre_topc(C_24, A_22) | v2_struct_0(C_24) | ~m1_pre_topc(B_23, A_22) | v2_struct_0(B_23) | ~l1_pre_topc(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_86])).
% 11.14/4.08  tff(c_38, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_170])).
% 11.14/4.08  tff(c_195, plain, (![A_81, B_82]: (k1_tsep_1(A_81, B_82, B_82)=g1_pre_topc(u1_struct_0(B_82), u1_pre_topc(B_82)) | ~m1_pre_topc(B_82, A_81) | v2_struct_0(B_82) | ~l1_pre_topc(A_81) | ~v2_pre_topc(A_81) | v2_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_124])).
% 11.14/4.08  tff(c_205, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=k1_tsep_1('#skF_1', '#skF_3', '#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_195])).
% 11.14/4.08  tff(c_220, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=k1_tsep_1('#skF_1', '#skF_3', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_205])).
% 11.14/4.08  tff(c_221, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=k1_tsep_1('#skF_1', '#skF_3', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_48, c_38, c_220])).
% 11.14/4.08  tff(c_28, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_170])).
% 11.14/4.08  tff(c_1210, plain, (![A_153, B_154, C_155]: (k1_tsep_1(A_153, B_154, C_155)=g1_pre_topc(u1_struct_0(C_155), u1_pre_topc(C_155)) | ~m1_pre_topc(B_154, C_155) | ~m1_pre_topc(C_155, A_153) | v2_struct_0(C_155) | ~m1_pre_topc(B_154, A_153) | v2_struct_0(B_154) | ~l1_pre_topc(A_153) | ~v2_pre_topc(A_153) | v2_struct_0(A_153))), inference(cnfTransformation, [status(thm)], [f_109])).
% 11.14/4.08  tff(c_1214, plain, (![A_153]: (k1_tsep_1(A_153, '#skF_4', '#skF_3')=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')) | ~m1_pre_topc('#skF_3', A_153) | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', A_153) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_153) | ~v2_pre_topc(A_153) | v2_struct_0(A_153))), inference(resolution, [status(thm)], [c_28, c_1210])).
% 11.14/4.08  tff(c_1225, plain, (![A_153]: (k1_tsep_1(A_153, '#skF_4', '#skF_3')=k1_tsep_1('#skF_1', '#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', A_153) | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', A_153) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_153) | ~v2_pre_topc(A_153) | v2_struct_0(A_153))), inference(demodulation, [status(thm), theory('equality')], [c_221, c_1214])).
% 11.14/4.08  tff(c_1292, plain, (![A_157]: (k1_tsep_1(A_157, '#skF_4', '#skF_3')=k1_tsep_1('#skF_1', '#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', A_157) | ~m1_pre_topc('#skF_4', A_157) | ~l1_pre_topc(A_157) | ~v2_pre_topc(A_157) | v2_struct_0(A_157))), inference(negUnitSimplification, [status(thm)], [c_34, c_38, c_1225])).
% 11.14/4.08  tff(c_1295, plain, (k1_tsep_1('#skF_1', '#skF_3', '#skF_3')=k1_tsep_1('#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_1292])).
% 11.14/4.08  tff(c_1298, plain, (k1_tsep_1('#skF_1', '#skF_3', '#skF_3')=k1_tsep_1('#skF_1', '#skF_4', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_32, c_1295])).
% 11.14/4.08  tff(c_1299, plain, (k1_tsep_1('#skF_1', '#skF_3', '#skF_3')=k1_tsep_1('#skF_1', '#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_48, c_1298])).
% 11.14/4.08  tff(c_1301, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=k1_tsep_1('#skF_1', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1299, c_221])).
% 11.14/4.08  tff(c_1369, plain, (![B_160, C_161, A_162]: (m1_pre_topc(B_160, C_161) | k1_tsep_1(A_162, B_160, C_161)!=g1_pre_topc(u1_struct_0(C_161), u1_pre_topc(C_161)) | ~m1_pre_topc(C_161, A_162) | v2_struct_0(C_161) | ~m1_pre_topc(B_160, A_162) | v2_struct_0(B_160) | ~l1_pre_topc(A_162) | ~v2_pre_topc(A_162) | v2_struct_0(A_162))), inference(cnfTransformation, [status(thm)], [f_109])).
% 11.14/4.08  tff(c_1371, plain, (![B_160, A_162]: (m1_pre_topc(B_160, '#skF_3') | k1_tsep_1(A_162, B_160, '#skF_3')!=k1_tsep_1('#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_3', A_162) | v2_struct_0('#skF_3') | ~m1_pre_topc(B_160, A_162) | v2_struct_0(B_160) | ~l1_pre_topc(A_162) | ~v2_pre_topc(A_162) | v2_struct_0(A_162))), inference(superposition, [status(thm), theory('equality')], [c_1301, c_1369])).
% 11.14/4.08  tff(c_16269, plain, (![B_545, A_546]: (m1_pre_topc(B_545, '#skF_3') | k1_tsep_1(A_546, B_545, '#skF_3')!=k1_tsep_1('#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_3', A_546) | ~m1_pre_topc(B_545, A_546) | v2_struct_0(B_545) | ~l1_pre_topc(A_546) | ~v2_pre_topc(A_546) | v2_struct_0(A_546))), inference(negUnitSimplification, [status(thm)], [c_38, c_1371])).
% 11.14/4.08  tff(c_16276, plain, (![B_545]: (m1_pre_topc(B_545, '#skF_3') | k1_tsep_1('#skF_1', B_545, '#skF_3')!=k1_tsep_1('#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc(B_545, '#skF_1') | v2_struct_0(B_545) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_16269])).
% 11.14/4.08  tff(c_16285, plain, (![B_545]: (m1_pre_topc(B_545, '#skF_3') | k1_tsep_1('#skF_1', B_545, '#skF_3')!=k1_tsep_1('#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc(B_545, '#skF_1') | v2_struct_0(B_545) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_16276])).
% 11.14/4.08  tff(c_16287, plain, (![B_547]: (m1_pre_topc(B_547, '#skF_3') | k1_tsep_1('#skF_1', B_547, '#skF_3')!=k1_tsep_1('#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc(B_547, '#skF_1') | v2_struct_0(B_547))), inference(negUnitSimplification, [status(thm)], [c_48, c_16285])).
% 11.14/4.08  tff(c_26, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_170])).
% 11.14/4.08  tff(c_16397, plain, (k1_tsep_1('#skF_1', k1_tsep_1('#skF_1', '#skF_2', '#skF_4'), '#skF_3')!=k1_tsep_1('#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_4'), '#skF_1') | v2_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_16287, c_26])).
% 11.14/4.08  tff(c_16883, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_4'), '#skF_1')), inference(splitLeft, [status(thm)], [c_16397])).
% 11.14/4.08  tff(c_16886, plain, (~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_10, c_16883])).
% 11.14/4.08  tff(c_16889, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_32, c_16886])).
% 11.14/4.08  tff(c_16891, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_42, c_34, c_16889])).
% 11.14/4.08  tff(c_16893, plain, (m1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_4'), '#skF_1')), inference(splitRight, [status(thm)], [c_16397])).
% 11.14/4.08  tff(c_83, plain, (![B_66, C_67, A_68]: (r1_tarski(u1_struct_0(B_66), u1_struct_0(C_67)) | ~m1_pre_topc(B_66, C_67) | ~m1_pre_topc(C_67, A_68) | ~m1_pre_topc(B_66, A_68) | ~l1_pre_topc(A_68) | ~v2_pre_topc(A_68))), inference(cnfTransformation, [status(thm)], [f_138])).
% 11.14/4.08  tff(c_93, plain, (![B_66]: (r1_tarski(u1_struct_0(B_66), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_66, '#skF_3') | ~m1_pre_topc(B_66, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_83])).
% 11.14/4.08  tff(c_104, plain, (![B_66]: (r1_tarski(u1_struct_0(B_66), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_66, '#skF_3') | ~m1_pre_topc(B_66, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_93])).
% 11.14/4.08  tff(c_30, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_170])).
% 11.14/4.08  tff(c_12, plain, (![A_22, B_23, C_24]: (v1_pre_topc(k1_tsep_1(A_22, B_23, C_24)) | ~m1_pre_topc(C_24, A_22) | v2_struct_0(C_24) | ~m1_pre_topc(B_23, A_22) | v2_struct_0(B_23) | ~l1_pre_topc(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_86])).
% 11.14/4.08  tff(c_6217, plain, (![A_314, B_315, C_316]: (u1_struct_0(k1_tsep_1(A_314, B_315, C_316))=k2_xboole_0(u1_struct_0(B_315), u1_struct_0(C_316)) | ~m1_pre_topc(k1_tsep_1(A_314, B_315, C_316), A_314) | ~v1_pre_topc(k1_tsep_1(A_314, B_315, C_316)) | v2_struct_0(k1_tsep_1(A_314, B_315, C_316)) | ~m1_pre_topc(C_316, A_314) | v2_struct_0(C_316) | ~m1_pre_topc(B_315, A_314) | v2_struct_0(B_315) | ~l1_pre_topc(A_314) | v2_struct_0(A_314))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.14/4.08  tff(c_6850, plain, (![A_328, B_329, C_330]: (u1_struct_0(k1_tsep_1(A_328, B_329, C_330))=k2_xboole_0(u1_struct_0(B_329), u1_struct_0(C_330)) | ~v1_pre_topc(k1_tsep_1(A_328, B_329, C_330)) | v2_struct_0(k1_tsep_1(A_328, B_329, C_330)) | ~m1_pre_topc(C_330, A_328) | v2_struct_0(C_330) | ~m1_pre_topc(B_329, A_328) | v2_struct_0(B_329) | ~l1_pre_topc(A_328) | v2_struct_0(A_328))), inference(resolution, [status(thm)], [c_10, c_6217])).
% 11.14/4.08  tff(c_87, plain, (![B_66]: (r1_tarski(u1_struct_0(B_66), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_66, '#skF_4') | ~m1_pre_topc(B_66, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_83])).
% 11.14/4.08  tff(c_97, plain, (![B_66]: (r1_tarski(u1_struct_0(B_66), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_66, '#skF_4') | ~m1_pre_topc(B_66, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_87])).
% 11.14/4.08  tff(c_18714, plain, (![B_597, C_598, A_599]: (r1_tarski(k2_xboole_0(u1_struct_0(B_597), u1_struct_0(C_598)), u1_struct_0('#skF_4')) | ~m1_pre_topc(k1_tsep_1(A_599, B_597, C_598), '#skF_4') | ~m1_pre_topc(k1_tsep_1(A_599, B_597, C_598), '#skF_1') | ~v1_pre_topc(k1_tsep_1(A_599, B_597, C_598)) | v2_struct_0(k1_tsep_1(A_599, B_597, C_598)) | ~m1_pre_topc(C_598, A_599) | v2_struct_0(C_598) | ~m1_pre_topc(B_597, A_599) | v2_struct_0(B_597) | ~l1_pre_topc(A_599) | v2_struct_0(A_599))), inference(superposition, [status(thm), theory('equality')], [c_6850, c_97])).
% 11.14/4.08  tff(c_18716, plain, (r1_tarski(k2_xboole_0(u1_struct_0('#skF_2'), u1_struct_0('#skF_4')), u1_struct_0('#skF_4')) | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_4'), '#skF_4') | ~v1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_4')) | v2_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_16893, c_18714])).
% 11.14/4.08  tff(c_18732, plain, (r1_tarski(k2_xboole_0(u1_struct_0('#skF_2'), u1_struct_0('#skF_4')), u1_struct_0('#skF_4')) | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_4'), '#skF_4') | ~v1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_4')) | v2_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_4')) | v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_32, c_18716])).
% 11.14/4.08  tff(c_18733, plain, (r1_tarski(k2_xboole_0(u1_struct_0('#skF_2'), u1_struct_0('#skF_4')), u1_struct_0('#skF_4')) | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_4'), '#skF_4') | ~v1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_4')) | v2_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_48, c_42, c_34, c_18732])).
% 11.14/4.08  tff(c_19359, plain, (~v1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_18733])).
% 11.14/4.08  tff(c_19362, plain, (~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_12, c_19359])).
% 11.14/4.08  tff(c_19365, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_32, c_19362])).
% 11.14/4.08  tff(c_19367, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_42, c_34, c_19365])).
% 11.14/4.08  tff(c_19369, plain, (v1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_18733])).
% 11.14/4.08  tff(c_14, plain, (![A_22, B_23, C_24]: (~v2_struct_0(k1_tsep_1(A_22, B_23, C_24)) | ~m1_pre_topc(C_24, A_22) | v2_struct_0(C_24) | ~m1_pre_topc(B_23, A_22) | v2_struct_0(B_23) | ~l1_pre_topc(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_86])).
% 11.14/4.08  tff(c_7066, plain, (![A_328, B_329, C_330]: (u1_struct_0(k1_tsep_1(A_328, B_329, C_330))=k2_xboole_0(u1_struct_0(B_329), u1_struct_0(C_330)) | ~v1_pre_topc(k1_tsep_1(A_328, B_329, C_330)) | ~m1_pre_topc(C_330, A_328) | v2_struct_0(C_330) | ~m1_pre_topc(B_329, A_328) | v2_struct_0(B_329) | ~l1_pre_topc(A_328) | v2_struct_0(A_328))), inference(resolution, [status(thm)], [c_6850, c_14])).
% 11.14/4.08  tff(c_19371, plain, (k2_xboole_0(u1_struct_0('#skF_2'), u1_struct_0('#skF_4'))=u1_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_19369, c_7066])).
% 11.14/4.08  tff(c_19374, plain, (k2_xboole_0(u1_struct_0('#skF_2'), u1_struct_0('#skF_4'))=u1_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_4')) | v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_32, c_19371])).
% 11.14/4.08  tff(c_19375, plain, (k2_xboole_0(u1_struct_0('#skF_2'), u1_struct_0('#skF_4'))=u1_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_48, c_42, c_34, c_19374])).
% 11.14/4.08  tff(c_1308, plain, (~v2_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1299, c_14])).
% 11.14/4.08  tff(c_1318, plain, (~v2_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_3')) | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_36, c_36, c_1308])).
% 11.14/4.08  tff(c_1319, plain, (~v2_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_48, c_38, c_1318])).
% 11.14/4.08  tff(c_1305, plain, (m1_pre_topc(k1_tsep_1('#skF_1', '#skF_4', '#skF_3'), '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1299, c_10])).
% 11.14/4.08  tff(c_1315, plain, (m1_pre_topc(k1_tsep_1('#skF_1', '#skF_4', '#skF_3'), '#skF_1') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_36, c_36, c_1305])).
% 11.14/4.08  tff(c_1316, plain, (m1_pre_topc(k1_tsep_1('#skF_1', '#skF_4', '#skF_3'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_48, c_38, c_1315])).
% 11.14/4.08  tff(c_234, plain, (![A_83, B_84, C_85]: (m1_pre_topc(k1_tsep_1(A_83, B_84, C_85), A_83) | ~m1_pre_topc(C_85, A_83) | v2_struct_0(C_85) | ~m1_pre_topc(B_84, A_83) | v2_struct_0(B_84) | ~l1_pre_topc(A_83) | v2_struct_0(A_83))), inference(cnfTransformation, [status(thm)], [f_86])).
% 11.14/4.08  tff(c_20, plain, (![A_32, B_34]: (k1_tsep_1(A_32, B_34, B_34)=g1_pre_topc(u1_struct_0(B_34), u1_pre_topc(B_34)) | ~m1_pre_topc(B_34, A_32) | v2_struct_0(B_34) | ~l1_pre_topc(A_32) | ~v2_pre_topc(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_124])).
% 11.14/4.08  tff(c_7310, plain, (![A_339, B_340, C_341]: (k1_tsep_1(A_339, k1_tsep_1(A_339, B_340, C_341), k1_tsep_1(A_339, B_340, C_341))=g1_pre_topc(u1_struct_0(k1_tsep_1(A_339, B_340, C_341)), u1_pre_topc(k1_tsep_1(A_339, B_340, C_341))) | v2_struct_0(k1_tsep_1(A_339, B_340, C_341)) | ~v2_pre_topc(A_339) | ~m1_pre_topc(C_341, A_339) | v2_struct_0(C_341) | ~m1_pre_topc(B_340, A_339) | v2_struct_0(B_340) | ~l1_pre_topc(A_339) | v2_struct_0(A_339))), inference(resolution, [status(thm)], [c_234, c_20])).
% 11.14/4.08  tff(c_16, plain, (![B_29, C_31, A_25]: (m1_pre_topc(B_29, C_31) | k1_tsep_1(A_25, B_29, C_31)!=g1_pre_topc(u1_struct_0(C_31), u1_pre_topc(C_31)) | ~m1_pre_topc(C_31, A_25) | v2_struct_0(C_31) | ~m1_pre_topc(B_29, A_25) | v2_struct_0(B_29) | ~l1_pre_topc(A_25) | ~v2_pre_topc(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_109])).
% 11.14/4.08  tff(c_10268, plain, (![A_419, B_420, C_421]: (m1_pre_topc(k1_tsep_1(A_419, B_420, C_421), k1_tsep_1(A_419, B_420, C_421)) | ~m1_pre_topc(k1_tsep_1(A_419, B_420, C_421), A_419) | v2_struct_0(k1_tsep_1(A_419, B_420, C_421)) | ~v2_pre_topc(A_419) | ~m1_pre_topc(C_421, A_419) | v2_struct_0(C_421) | ~m1_pre_topc(B_420, A_419) | v2_struct_0(B_420) | ~l1_pre_topc(A_419) | v2_struct_0(A_419))), inference(superposition, [status(thm), theory('equality')], [c_7310, c_16])).
% 11.14/4.08  tff(c_1220, plain, (![A_153]: (k1_tsep_1(A_153, '#skF_2', '#skF_3')=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')) | ~m1_pre_topc('#skF_3', A_153) | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', A_153) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_153) | ~v2_pre_topc(A_153) | v2_struct_0(A_153))), inference(resolution, [status(thm)], [c_30, c_1210])).
% 11.14/4.08  tff(c_1234, plain, (![A_153]: (k1_tsep_1(A_153, '#skF_2', '#skF_3')=k1_tsep_1('#skF_1', '#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', A_153) | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', A_153) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_153) | ~v2_pre_topc(A_153) | v2_struct_0(A_153))), inference(demodulation, [status(thm), theory('equality')], [c_221, c_1220])).
% 11.14/4.08  tff(c_1235, plain, (![A_153]: (k1_tsep_1(A_153, '#skF_2', '#skF_3')=k1_tsep_1('#skF_1', '#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', A_153) | ~m1_pre_topc('#skF_2', A_153) | ~l1_pre_topc(A_153) | ~v2_pre_topc(A_153) | v2_struct_0(A_153))), inference(negUnitSimplification, [status(thm)], [c_42, c_38, c_1234])).
% 11.14/4.08  tff(c_1356, plain, (![A_159]: (k1_tsep_1(A_159, '#skF_2', '#skF_3')=k1_tsep_1('#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_3', A_159) | ~m1_pre_topc('#skF_2', A_159) | ~l1_pre_topc(A_159) | ~v2_pre_topc(A_159) | v2_struct_0(A_159))), inference(demodulation, [status(thm), theory('equality')], [c_1299, c_1235])).
% 11.14/4.08  tff(c_1359, plain, (k1_tsep_1('#skF_1', '#skF_2', '#skF_3')=k1_tsep_1('#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_1356])).
% 11.14/4.08  tff(c_1365, plain, (k1_tsep_1('#skF_1', '#skF_2', '#skF_3')=k1_tsep_1('#skF_1', '#skF_4', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_36, c_1359])).
% 11.14/4.08  tff(c_1366, plain, (k1_tsep_1('#skF_1', '#skF_2', '#skF_3')=k1_tsep_1('#skF_1', '#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_48, c_1365])).
% 11.14/4.08  tff(c_1311, plain, (v1_pre_topc(k1_tsep_1('#skF_1', '#skF_4', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1299, c_12])).
% 11.14/4.08  tff(c_1321, plain, (v1_pre_topc(k1_tsep_1('#skF_1', '#skF_4', '#skF_3')) | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_36, c_36, c_1311])).
% 11.14/4.08  tff(c_1322, plain, (v1_pre_topc(k1_tsep_1('#skF_1', '#skF_4', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_48, c_38, c_1321])).
% 11.14/4.08  tff(c_6219, plain, (k2_xboole_0(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))=u1_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_4', '#skF_3'), '#skF_1') | ~v1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_3')) | v2_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1366, c_6217])).
% 11.14/4.08  tff(c_6227, plain, (k2_xboole_0(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))=u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_3')) | v2_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_3')) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_36, c_1366, c_1322, c_1366, c_1316, c_1366, c_6219])).
% 11.14/4.08  tff(c_6228, plain, (k2_xboole_0(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))=u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_48, c_42, c_38, c_1319, c_6227])).
% 11.14/4.08  tff(c_122, plain, (![B_71]: (r1_tarski(u1_struct_0(B_71), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_71, '#skF_3') | ~m1_pre_topc(B_71, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_93])).
% 11.14/4.08  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(A_1, B_2)=B_2 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.14/4.08  tff(c_129, plain, (![B_71]: (k2_xboole_0(u1_struct_0(B_71), u1_struct_0('#skF_3'))=u1_struct_0('#skF_3') | ~m1_pre_topc(B_71, '#skF_3') | ~m1_pre_topc(B_71, '#skF_1'))), inference(resolution, [status(thm)], [c_122, c_2])).
% 11.14/4.08  tff(c_6320, plain, (u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_3'))=u1_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6228, c_129])).
% 11.14/4.08  tff(c_6349, plain, (u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_3'))=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_30, c_6320])).
% 11.14/4.08  tff(c_22, plain, (![B_39, C_41, A_35]: (r1_tarski(u1_struct_0(B_39), u1_struct_0(C_41)) | ~m1_pre_topc(B_39, C_41) | ~m1_pre_topc(C_41, A_35) | ~m1_pre_topc(B_39, A_35) | ~l1_pre_topc(A_35) | ~v2_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_138])).
% 11.14/4.08  tff(c_6666, plain, (![B_319, A_320, B_321, C_322]: (r1_tarski(u1_struct_0(B_319), u1_struct_0(k1_tsep_1(A_320, B_321, C_322))) | ~m1_pre_topc(B_319, k1_tsep_1(A_320, B_321, C_322)) | ~m1_pre_topc(B_319, A_320) | ~v2_pre_topc(A_320) | ~m1_pre_topc(C_322, A_320) | v2_struct_0(C_322) | ~m1_pre_topc(B_321, A_320) | v2_struct_0(B_321) | ~l1_pre_topc(A_320) | v2_struct_0(A_320))), inference(resolution, [status(thm)], [c_234, c_22])).
% 11.14/4.08  tff(c_6690, plain, (![B_319]: (r1_tarski(u1_struct_0(B_319), u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_3'))) | ~m1_pre_topc(B_319, k1_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~m1_pre_topc(B_319, '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1366, c_6666])).
% 11.14/4.08  tff(c_6705, plain, (![B_319]: (r1_tarski(u1_struct_0(B_319), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_319, k1_tsep_1('#skF_1', '#skF_4', '#skF_3')) | ~m1_pre_topc(B_319, '#skF_1') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_36, c_46, c_1366, c_6349, c_6690])).
% 11.14/4.08  tff(c_6711, plain, (![B_323]: (r1_tarski(u1_struct_0(B_323), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_323, k1_tsep_1('#skF_1', '#skF_4', '#skF_3')) | ~m1_pre_topc(B_323, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_48, c_42, c_38, c_6705])).
% 11.14/4.08  tff(c_6729, plain, (r1_tarski(u1_struct_0('#skF_3'), u1_struct_0('#skF_3')) | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_4', '#skF_3'), k1_tsep_1('#skF_1', '#skF_4', '#skF_3')) | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_4', '#skF_3'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6349, c_6711])).
% 11.14/4.08  tff(c_6742, plain, (r1_tarski(u1_struct_0('#skF_3'), u1_struct_0('#skF_3')) | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_4', '#skF_3'), k1_tsep_1('#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1316, c_6729])).
% 11.14/4.08  tff(c_7135, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_4', '#skF_3'), k1_tsep_1('#skF_1', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_6742])).
% 11.14/4.08  tff(c_10275, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_4', '#skF_3'), '#skF_1') | v2_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_3')) | ~v2_pre_topc('#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_10268, c_7135])).
% 11.14/4.08  tff(c_10310, plain, (v2_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_3')) | v2_struct_0('#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_32, c_36, c_46, c_1316, c_10275])).
% 11.14/4.08  tff(c_10312, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_34, c_38, c_1319, c_10310])).
% 11.14/4.08  tff(c_10313, plain, (r1_tarski(u1_struct_0('#skF_3'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_6742])).
% 11.14/4.08  tff(c_24, plain, (![B_39, C_41, A_35]: (m1_pre_topc(B_39, C_41) | ~r1_tarski(u1_struct_0(B_39), u1_struct_0(C_41)) | ~m1_pre_topc(C_41, A_35) | ~m1_pre_topc(B_39, A_35) | ~l1_pre_topc(A_35) | ~v2_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_138])).
% 11.14/4.08  tff(c_10345, plain, (![A_35]: (m1_pre_topc('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', A_35) | ~l1_pre_topc(A_35) | ~v2_pre_topc(A_35))), inference(resolution, [status(thm)], [c_10313, c_24])).
% 11.14/4.08  tff(c_10368, plain, (![A_422]: (~m1_pre_topc('#skF_3', A_422) | ~l1_pre_topc(A_422) | ~v2_pre_topc(A_422))), inference(splitLeft, [status(thm)], [c_10345])).
% 11.14/4.08  tff(c_10371, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_10368])).
% 11.14/4.08  tff(c_10375, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_10371])).
% 11.14/4.08  tff(c_10376, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_10345])).
% 11.14/4.08  tff(c_172, plain, (![B_74]: (k2_xboole_0(u1_struct_0(B_74), u1_struct_0('#skF_3'))=u1_struct_0('#skF_3') | ~m1_pre_topc(B_74, '#skF_3') | ~m1_pre_topc(B_74, '#skF_1'))), inference(resolution, [status(thm)], [c_122, c_2])).
% 11.14/4.08  tff(c_4, plain, (![A_3, C_5, B_4, D_6]: (r1_tarski(k2_xboole_0(A_3, C_5), k2_xboole_0(B_4, D_6)) | ~r1_tarski(C_5, D_6) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.14/4.08  tff(c_1432, plain, (![A_168, C_169, B_170]: (r1_tarski(k2_xboole_0(A_168, C_169), u1_struct_0('#skF_3')) | ~r1_tarski(C_169, u1_struct_0('#skF_3')) | ~r1_tarski(A_168, u1_struct_0(B_170)) | ~m1_pre_topc(B_170, '#skF_3') | ~m1_pre_topc(B_170, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_172, c_4])).
% 11.14/4.08  tff(c_1436, plain, (![B_66, C_169]: (r1_tarski(k2_xboole_0(u1_struct_0(B_66), C_169), u1_struct_0('#skF_3')) | ~r1_tarski(C_169, u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc(B_66, '#skF_3') | ~m1_pre_topc(B_66, '#skF_1'))), inference(resolution, [status(thm)], [c_104, c_1432])).
% 11.14/4.08  tff(c_1446, plain, (![B_66, C_169]: (r1_tarski(k2_xboole_0(u1_struct_0(B_66), C_169), u1_struct_0('#skF_3')) | ~r1_tarski(C_169, u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_3') | ~m1_pre_topc(B_66, '#skF_3') | ~m1_pre_topc(B_66, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1436])).
% 11.14/4.08  tff(c_13822, plain, (![B_66, C_169]: (r1_tarski(k2_xboole_0(u1_struct_0(B_66), C_169), u1_struct_0('#skF_3')) | ~r1_tarski(C_169, u1_struct_0('#skF_3')) | ~m1_pre_topc(B_66, '#skF_3') | ~m1_pre_topc(B_66, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_10376, c_1446])).
% 11.14/4.08  tff(c_19417, plain, (r1_tarski(u1_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_4')), u1_struct_0('#skF_3')) | ~r1_tarski(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_19375, c_13822])).
% 11.14/4.08  tff(c_19526, plain, (r1_tarski(u1_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_4')), u1_struct_0('#skF_3')) | ~r1_tarski(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_30, c_19417])).
% 11.14/4.08  tff(c_19801, plain, (~r1_tarski(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_19526])).
% 11.14/4.08  tff(c_19807, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_104, c_19801])).
% 11.14/4.08  tff(c_19814, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_19807])).
% 11.14/4.08  tff(c_19815, plain, (r1_tarski(u1_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_4')), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_19526])).
% 11.14/4.08  tff(c_19872, plain, (![A_35]: (m1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_4'), '#skF_3') | ~m1_pre_topc('#skF_3', A_35) | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_4'), A_35) | ~l1_pre_topc(A_35) | ~v2_pre_topc(A_35))), inference(resolution, [status(thm)], [c_19815, c_24])).
% 11.14/4.08  tff(c_20386, plain, (![A_615]: (~m1_pre_topc('#skF_3', A_615) | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_4'), A_615) | ~l1_pre_topc(A_615) | ~v2_pre_topc(A_615))), inference(negUnitSimplification, [status(thm)], [c_26, c_19872])).
% 11.14/4.08  tff(c_20389, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16893, c_20386])).
% 11.14/4.08  tff(c_20409, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_36, c_20389])).
% 11.14/4.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.14/4.08  
% 11.14/4.08  Inference rules
% 11.14/4.08  ----------------------
% 11.14/4.08  #Ref     : 0
% 11.14/4.08  #Sup     : 5013
% 11.14/4.08  #Fact    : 0
% 11.14/4.08  #Define  : 0
% 11.14/4.08  #Split   : 72
% 11.14/4.08  #Chain   : 0
% 11.14/4.08  #Close   : 0
% 11.14/4.08  
% 11.14/4.08  Ordering : KBO
% 11.14/4.08  
% 11.14/4.08  Simplification rules
% 11.14/4.08  ----------------------
% 11.14/4.08  #Subsume      : 1224
% 11.14/4.08  #Demod        : 3521
% 11.14/4.08  #Tautology    : 1766
% 11.14/4.08  #SimpNegUnit  : 538
% 11.14/4.08  #BackRed      : 17
% 11.14/4.08  
% 11.14/4.08  #Partial instantiations: 0
% 11.14/4.08  #Strategies tried      : 1
% 11.14/4.08  
% 11.14/4.08  Timing (in seconds)
% 11.14/4.08  ----------------------
% 11.14/4.09  Preprocessing        : 0.33
% 11.14/4.09  Parsing              : 0.18
% 11.14/4.09  CNF conversion       : 0.03
% 11.14/4.09  Main loop            : 2.98
% 11.14/4.09  Inferencing          : 0.81
% 11.14/4.09  Reduction            : 0.98
% 11.14/4.09  Demodulation         : 0.68
% 11.14/4.09  BG Simplification    : 0.11
% 11.14/4.09  Subsumption          : 0.90
% 11.14/4.09  Abstraction          : 0.15
% 11.14/4.09  MUC search           : 0.00
% 11.14/4.09  Cooper               : 0.00
% 11.14/4.09  Total                : 3.36
% 11.14/4.09  Index Insertion      : 0.00
% 11.14/4.09  Index Deletion       : 0.00
% 11.14/4.09  Index Matching       : 0.00
% 11.14/4.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
