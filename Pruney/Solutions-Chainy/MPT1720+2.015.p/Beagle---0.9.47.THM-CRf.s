%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:43 EST 2020

% Result     : Theorem 8.44s
% Output     : CNFRefutation 8.66s
% Verified   : 
% Statistics : Number of formulae       :  133 (2839 expanded)
%              Number of leaves         :   26 (1089 expanded)
%              Depth                    :   24
%              Number of atoms          :  526 (17153 expanded)
%              Number of equality atoms :   49 ( 850 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_201,negated_conjecture,(
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

tff(f_80,axiom,(
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

tff(f_118,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => k1_tsep_1(A,B,B) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tmap_1)).

tff(f_103,axiom,(
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

tff(f_155,axiom,(
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
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,A) )
                 => ! [E] :
                      ( ( ~ v2_struct_0(E)
                        & m1_pre_topc(E,A) )
                     => ( ( m1_pre_topc(B,C)
                          & m1_pre_topc(D,E) )
                       => m1_pre_topc(k1_tsep_1(A,B,D),k1_tsep_1(A,C,E)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tmap_1)).

tff(f_58,axiom,(
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

tff(f_169,axiom,(
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

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_26,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_44,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_40,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_32,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_8,plain,(
    ! [A_18,B_19,C_20] :
      ( m1_pre_topc(k1_tsep_1(A_18,B_19,C_20),A_18)
      | ~ m1_pre_topc(C_20,A_18)
      | v2_struct_0(C_20)
      | ~ m1_pre_topc(B_19,A_18)
      | v2_struct_0(B_19)
      | ~ l1_pre_topc(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_46,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_36,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_131,plain,(
    ! [A_103,B_104] :
      ( k1_tsep_1(A_103,B_104,B_104) = g1_pre_topc(u1_struct_0(B_104),u1_pre_topc(B_104))
      | ~ m1_pre_topc(B_104,A_103)
      | v2_struct_0(B_104)
      | ~ l1_pre_topc(A_103)
      | ~ v2_pre_topc(A_103)
      | v2_struct_0(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_143,plain,
    ( g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = k1_tsep_1('#skF_1','#skF_3','#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_131])).

tff(c_159,plain,
    ( g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = k1_tsep_1('#skF_1','#skF_3','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_143])).

tff(c_160,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = k1_tsep_1('#skF_1','#skF_3','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_38,c_159])).

tff(c_173,plain,(
    ! [B_105,C_106,A_107] :
      ( m1_pre_topc(B_105,C_106)
      | k1_tsep_1(A_107,B_105,C_106) != g1_pre_topc(u1_struct_0(C_106),u1_pre_topc(C_106))
      | ~ m1_pre_topc(C_106,A_107)
      | v2_struct_0(C_106)
      | ~ m1_pre_topc(B_105,A_107)
      | v2_struct_0(B_105)
      | ~ l1_pre_topc(A_107)
      | ~ v2_pre_topc(A_107)
      | v2_struct_0(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_175,plain,(
    ! [B_105,A_107] :
      ( m1_pre_topc(B_105,'#skF_3')
      | k1_tsep_1(A_107,B_105,'#skF_3') != k1_tsep_1('#skF_1','#skF_3','#skF_3')
      | ~ m1_pre_topc('#skF_3',A_107)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_105,A_107)
      | v2_struct_0(B_105)
      | ~ l1_pre_topc(A_107)
      | ~ v2_pre_topc(A_107)
      | v2_struct_0(A_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_173])).

tff(c_183,plain,(
    ! [B_108,A_109] :
      ( m1_pre_topc(B_108,'#skF_3')
      | k1_tsep_1(A_109,B_108,'#skF_3') != k1_tsep_1('#skF_1','#skF_3','#skF_3')
      | ~ m1_pre_topc('#skF_3',A_109)
      | ~ m1_pre_topc(B_108,A_109)
      | v2_struct_0(B_108)
      | ~ l1_pre_topc(A_109)
      | ~ v2_pre_topc(A_109)
      | v2_struct_0(A_109) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_175])).

tff(c_185,plain,(
    ! [B_108] :
      ( m1_pre_topc(B_108,'#skF_3')
      | k1_tsep_1('#skF_1',B_108,'#skF_3') != k1_tsep_1('#skF_1','#skF_3','#skF_3')
      | ~ m1_pre_topc(B_108,'#skF_1')
      | v2_struct_0(B_108)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_36,c_183])).

tff(c_188,plain,(
    ! [B_108] :
      ( m1_pre_topc(B_108,'#skF_3')
      | k1_tsep_1('#skF_1',B_108,'#skF_3') != k1_tsep_1('#skF_1','#skF_3','#skF_3')
      | ~ m1_pre_topc(B_108,'#skF_1')
      | v2_struct_0(B_108)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_185])).

tff(c_190,plain,(
    ! [B_110] :
      ( m1_pre_topc(B_110,'#skF_3')
      | k1_tsep_1('#skF_1',B_110,'#skF_3') != k1_tsep_1('#skF_1','#skF_3','#skF_3')
      | ~ m1_pre_topc(B_110,'#skF_1')
      | v2_struct_0(B_110) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_188])).

tff(c_208,plain,
    ( k1_tsep_1('#skF_1',k1_tsep_1('#skF_1','#skF_2','#skF_4'),'#skF_3') != k1_tsep_1('#skF_1','#skF_3','#skF_3')
    | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_4'),'#skF_1')
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_190,c_26])).

tff(c_209,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_4'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_208])).

tff(c_246,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_209])).

tff(c_249,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_32,c_246])).

tff(c_251,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_42,c_34,c_249])).

tff(c_253,plain,(
    m1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_4'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_208])).

tff(c_30,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_28,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_329,plain,(
    ! [A_117,B_118,C_119] :
      ( k1_tsep_1(A_117,B_118,C_119) = g1_pre_topc(u1_struct_0(C_119),u1_pre_topc(C_119))
      | ~ m1_pre_topc(B_118,C_119)
      | ~ m1_pre_topc(C_119,A_117)
      | v2_struct_0(C_119)
      | ~ m1_pre_topc(B_118,A_117)
      | v2_struct_0(B_118)
      | ~ l1_pre_topc(A_117)
      | ~ v2_pre_topc(A_117)
      | v2_struct_0(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_339,plain,(
    ! [A_117] :
      ( k1_tsep_1(A_117,'#skF_4','#skF_3') = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_117)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_4',A_117)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_117)
      | ~ v2_pre_topc(A_117)
      | v2_struct_0(A_117) ) ),
    inference(resolution,[status(thm)],[c_28,c_329])).

tff(c_359,plain,(
    ! [A_117] :
      ( k1_tsep_1(A_117,'#skF_4','#skF_3') = k1_tsep_1('#skF_1','#skF_3','#skF_3')
      | ~ m1_pre_topc('#skF_3',A_117)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_4',A_117)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_117)
      | ~ v2_pre_topc(A_117)
      | v2_struct_0(A_117) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_339])).

tff(c_495,plain,(
    ! [A_128] :
      ( k1_tsep_1(A_128,'#skF_4','#skF_3') = k1_tsep_1('#skF_1','#skF_3','#skF_3')
      | ~ m1_pre_topc('#skF_3',A_128)
      | ~ m1_pre_topc('#skF_4',A_128)
      | ~ l1_pre_topc(A_128)
      | ~ v2_pre_topc(A_128)
      | v2_struct_0(A_128) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_38,c_359])).

tff(c_502,plain,
    ( k1_tsep_1('#skF_1','#skF_3','#skF_3') = k1_tsep_1('#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_495])).

tff(c_509,plain,
    ( k1_tsep_1('#skF_1','#skF_3','#skF_3') = k1_tsep_1('#skF_1','#skF_4','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_32,c_502])).

tff(c_510,plain,(
    k1_tsep_1('#skF_1','#skF_3','#skF_3') = k1_tsep_1('#skF_1','#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_509])).

tff(c_641,plain,(
    ! [C_132,E_133,D_136,B_134,A_135] :
      ( m1_pre_topc(k1_tsep_1(A_135,B_134,D_136),k1_tsep_1(A_135,C_132,E_133))
      | ~ m1_pre_topc(D_136,E_133)
      | ~ m1_pre_topc(B_134,C_132)
      | ~ m1_pre_topc(E_133,A_135)
      | v2_struct_0(E_133)
      | ~ m1_pre_topc(D_136,A_135)
      | v2_struct_0(D_136)
      | ~ m1_pre_topc(C_132,A_135)
      | v2_struct_0(C_132)
      | ~ m1_pre_topc(B_134,A_135)
      | v2_struct_0(B_134)
      | ~ l1_pre_topc(A_135)
      | ~ v2_pre_topc(A_135)
      | v2_struct_0(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_659,plain,(
    ! [B_134,D_136] :
      ( m1_pre_topc(k1_tsep_1('#skF_1',B_134,D_136),k1_tsep_1('#skF_1','#skF_4','#skF_3'))
      | ~ m1_pre_topc(D_136,'#skF_3')
      | ~ m1_pre_topc(B_134,'#skF_3')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(D_136,'#skF_1')
      | v2_struct_0(D_136)
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_134,'#skF_1')
      | v2_struct_0(B_134)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_510,c_641])).

tff(c_673,plain,(
    ! [B_134,D_136] :
      ( m1_pre_topc(k1_tsep_1('#skF_1',B_134,D_136),k1_tsep_1('#skF_1','#skF_4','#skF_3'))
      | ~ m1_pre_topc(D_136,'#skF_3')
      | ~ m1_pre_topc(B_134,'#skF_3')
      | ~ m1_pre_topc(D_136,'#skF_1')
      | v2_struct_0(D_136)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_134,'#skF_1')
      | v2_struct_0(B_134)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_36,c_36,c_659])).

tff(c_674,plain,(
    ! [B_134,D_136] :
      ( m1_pre_topc(k1_tsep_1('#skF_1',B_134,D_136),k1_tsep_1('#skF_1','#skF_4','#skF_3'))
      | ~ m1_pre_topc(D_136,'#skF_3')
      | ~ m1_pre_topc(B_134,'#skF_3')
      | ~ m1_pre_topc(D_136,'#skF_1')
      | v2_struct_0(D_136)
      | ~ m1_pre_topc(B_134,'#skF_1')
      | v2_struct_0(B_134) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_38,c_673])).

tff(c_10,plain,(
    ! [A_18,B_19,C_20] :
      ( v1_pre_topc(k1_tsep_1(A_18,B_19,C_20))
      | ~ m1_pre_topc(C_20,A_18)
      | v2_struct_0(C_20)
      | ~ m1_pre_topc(B_19,A_18)
      | v2_struct_0(B_19)
      | ~ l1_pre_topc(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_545,plain,(
    ! [A_129,B_130,C_131] :
      ( u1_struct_0(k1_tsep_1(A_129,B_130,C_131)) = k2_xboole_0(u1_struct_0(B_130),u1_struct_0(C_131))
      | ~ m1_pre_topc(k1_tsep_1(A_129,B_130,C_131),A_129)
      | ~ v1_pre_topc(k1_tsep_1(A_129,B_130,C_131))
      | v2_struct_0(k1_tsep_1(A_129,B_130,C_131))
      | ~ m1_pre_topc(C_131,A_129)
      | v2_struct_0(C_131)
      | ~ m1_pre_topc(B_130,A_129)
      | v2_struct_0(B_130)
      | ~ l1_pre_topc(A_129)
      | v2_struct_0(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_549,plain,
    ( k2_xboole_0(u1_struct_0('#skF_2'),u1_struct_0('#skF_4')) = u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_4'))
    | ~ v1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_4'))
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_253,c_545])).

tff(c_557,plain,
    ( k2_xboole_0(u1_struct_0('#skF_2'),u1_struct_0('#skF_4')) = u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_4'))
    | ~ v1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_4'))
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_4'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_32,c_549])).

tff(c_558,plain,
    ( k2_xboole_0(u1_struct_0('#skF_2'),u1_struct_0('#skF_4')) = u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_4'))
    | ~ v1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_4'))
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_42,c_34,c_557])).

tff(c_1962,plain,(
    ~ v1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_558])).

tff(c_1965,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_1962])).

tff(c_1968,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_32,c_1965])).

tff(c_1970,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_42,c_34,c_1968])).

tff(c_1971,plain,
    ( v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_4'))
    | k2_xboole_0(u1_struct_0('#skF_2'),u1_struct_0('#skF_4')) = u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_558])).

tff(c_2002,plain,(
    k2_xboole_0(u1_struct_0('#skF_2'),u1_struct_0('#skF_4')) = u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1971])).

tff(c_2028,plain,(
    ! [A_181,B_182,C_183] :
      ( u1_struct_0(k1_tsep_1(A_181,B_182,C_183)) = k2_xboole_0(u1_struct_0(B_182),u1_struct_0(C_183))
      | ~ v1_pre_topc(k1_tsep_1(A_181,B_182,C_183))
      | v2_struct_0(k1_tsep_1(A_181,B_182,C_183))
      | ~ m1_pre_topc(C_183,A_181)
      | v2_struct_0(C_183)
      | ~ m1_pre_topc(B_182,A_181)
      | v2_struct_0(B_182)
      | ~ l1_pre_topc(A_181)
      | v2_struct_0(A_181) ) ),
    inference(resolution,[status(thm)],[c_8,c_545])).

tff(c_12,plain,(
    ! [A_18,B_19,C_20] :
      ( ~ v2_struct_0(k1_tsep_1(A_18,B_19,C_20))
      | ~ m1_pre_topc(C_20,A_18)
      | v2_struct_0(C_20)
      | ~ m1_pre_topc(B_19,A_18)
      | v2_struct_0(B_19)
      | ~ l1_pre_topc(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_3630,plain,(
    ! [A_235,B_236,C_237] :
      ( u1_struct_0(k1_tsep_1(A_235,B_236,C_237)) = k2_xboole_0(u1_struct_0(B_236),u1_struct_0(C_237))
      | ~ v1_pre_topc(k1_tsep_1(A_235,B_236,C_237))
      | ~ m1_pre_topc(C_237,A_235)
      | v2_struct_0(C_237)
      | ~ m1_pre_topc(B_236,A_235)
      | v2_struct_0(B_236)
      | ~ l1_pre_topc(A_235)
      | v2_struct_0(A_235) ) ),
    inference(resolution,[status(thm)],[c_2028,c_12])).

tff(c_3664,plain,(
    ! [A_238,B_239,C_240] :
      ( u1_struct_0(k1_tsep_1(A_238,B_239,C_240)) = k2_xboole_0(u1_struct_0(B_239),u1_struct_0(C_240))
      | ~ m1_pre_topc(C_240,A_238)
      | v2_struct_0(C_240)
      | ~ m1_pre_topc(B_239,A_238)
      | v2_struct_0(B_239)
      | ~ l1_pre_topc(A_238)
      | v2_struct_0(A_238) ) ),
    inference(resolution,[status(thm)],[c_10,c_3630])).

tff(c_3798,plain,(
    ! [A_238] :
      ( u1_struct_0(k1_tsep_1(A_238,'#skF_2','#skF_4')) = u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_4'))
      | ~ m1_pre_topc('#skF_4',A_238)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_2',A_238)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_238)
      | v2_struct_0(A_238) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2002,c_3664])).

tff(c_4348,plain,(
    ! [A_247] :
      ( u1_struct_0(k1_tsep_1(A_247,'#skF_2','#skF_4')) = u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_4'))
      | ~ m1_pre_topc('#skF_4',A_247)
      | ~ m1_pre_topc('#skF_2',A_247)
      | ~ l1_pre_topc(A_247)
      | v2_struct_0(A_247) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_34,c_3798])).

tff(c_345,plain,(
    ! [A_117] :
      ( k1_tsep_1(A_117,'#skF_2','#skF_3') = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_117)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_2',A_117)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_117)
      | ~ v2_pre_topc(A_117)
      | v2_struct_0(A_117) ) ),
    inference(resolution,[status(thm)],[c_30,c_329])).

tff(c_368,plain,(
    ! [A_117] :
      ( k1_tsep_1(A_117,'#skF_2','#skF_3') = k1_tsep_1('#skF_1','#skF_3','#skF_3')
      | ~ m1_pre_topc('#skF_3',A_117)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_2',A_117)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_117)
      | ~ v2_pre_topc(A_117)
      | v2_struct_0(A_117) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_345])).

tff(c_411,plain,(
    ! [A_122] :
      ( k1_tsep_1(A_122,'#skF_2','#skF_3') = k1_tsep_1('#skF_1','#skF_3','#skF_3')
      | ~ m1_pre_topc('#skF_3',A_122)
      | ~ m1_pre_topc('#skF_2',A_122)
      | ~ l1_pre_topc(A_122)
      | ~ v2_pre_topc(A_122)
      | v2_struct_0(A_122) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_38,c_368])).

tff(c_418,plain,
    ( k1_tsep_1('#skF_1','#skF_2','#skF_3') = k1_tsep_1('#skF_1','#skF_3','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_411])).

tff(c_428,plain,
    ( k1_tsep_1('#skF_1','#skF_2','#skF_3') = k1_tsep_1('#skF_1','#skF_3','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_36,c_418])).

tff(c_429,plain,(
    k1_tsep_1('#skF_1','#skF_2','#skF_3') = k1_tsep_1('#skF_1','#skF_3','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_428])).

tff(c_451,plain,
    ( ~ v2_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_429,c_12])).

tff(c_461,plain,
    ( ~ v2_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_36,c_451])).

tff(c_462,plain,(
    ~ v2_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_42,c_38,c_461])).

tff(c_515,plain,(
    ~ v2_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_510,c_462])).

tff(c_517,plain,(
    k1_tsep_1('#skF_1','#skF_2','#skF_3') = k1_tsep_1('#skF_1','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_510,c_429])).

tff(c_448,plain,
    ( v1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_429,c_10])).

tff(c_458,plain,
    ( v1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_36,c_448])).

tff(c_459,plain,(
    v1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_42,c_38,c_458])).

tff(c_516,plain,(
    v1_pre_topc(k1_tsep_1('#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_510,c_459])).

tff(c_445,plain,
    ( m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_3'),'#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_429,c_8])).

tff(c_455,plain,
    ( m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_3'),'#skF_1')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_36,c_445])).

tff(c_456,plain,(
    m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_3'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_42,c_38,c_455])).

tff(c_514,plain,(
    m1_pre_topc(k1_tsep_1('#skF_1','#skF_4','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_510,c_456])).

tff(c_6,plain,(
    ! [A_3,B_11,C_15] :
      ( u1_struct_0(k1_tsep_1(A_3,B_11,C_15)) = k2_xboole_0(u1_struct_0(B_11),u1_struct_0(C_15))
      | ~ m1_pre_topc(k1_tsep_1(A_3,B_11,C_15),A_3)
      | ~ v1_pre_topc(k1_tsep_1(A_3,B_11,C_15))
      | v2_struct_0(k1_tsep_1(A_3,B_11,C_15))
      | ~ m1_pre_topc(C_15,A_3)
      | v2_struct_0(C_15)
      | ~ m1_pre_topc(B_11,A_3)
      | v2_struct_0(B_11)
      | ~ l1_pre_topc(A_3)
      | v2_struct_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_592,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_517,c_6])).

tff(c_605,plain,
    ( k2_xboole_0(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) = u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_3'))
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_36,c_517,c_516,c_517,c_514,c_517,c_592])).

tff(c_606,plain,(
    k2_xboole_0(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) = u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_42,c_38,c_515,c_605])).

tff(c_51,plain,(
    ! [B_85,C_86,A_87] :
      ( r1_tarski(u1_struct_0(B_85),u1_struct_0(C_86))
      | ~ m1_pre_topc(B_85,C_86)
      | ~ m1_pre_topc(C_86,A_87)
      | ~ m1_pre_topc(B_85,A_87)
      | ~ l1_pre_topc(A_87)
      | ~ v2_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_61,plain,(
    ! [B_85] :
      ( r1_tarski(u1_struct_0(B_85),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_85,'#skF_3')
      | ~ m1_pre_topc(B_85,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_36,c_51])).

tff(c_82,plain,(
    ! [B_92] :
      ( r1_tarski(u1_struct_0(B_92),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_92,'#skF_3')
      | ~ m1_pre_topc(B_92,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_61])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k2_xboole_0(A_1,B_2) = B_2
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_89,plain,(
    ! [B_92] :
      ( k2_xboole_0(u1_struct_0(B_92),u1_struct_0('#skF_3')) = u1_struct_0('#skF_3')
      | ~ m1_pre_topc(B_92,'#skF_3')
      | ~ m1_pre_topc(B_92,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_82,c_2])).

tff(c_629,plain,
    ( u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_3')) = u1_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_606,c_89])).

tff(c_637,plain,(
    u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_3')) = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_30,c_629])).

tff(c_22,plain,(
    ! [B_66,C_68,A_62] :
      ( r1_tarski(u1_struct_0(B_66),u1_struct_0(C_68))
      | ~ m1_pre_topc(B_66,C_68)
      | ~ m1_pre_topc(C_68,A_62)
      | ~ m1_pre_topc(B_66,A_62)
      | ~ l1_pre_topc(A_62)
      | ~ v2_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_472,plain,(
    ! [B_66] :
      ( r1_tarski(u1_struct_0(B_66),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_3')))
      | ~ m1_pre_topc(B_66,k1_tsep_1('#skF_1','#skF_3','#skF_3'))
      | ~ m1_pre_topc(B_66,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_456,c_22])).

tff(c_485,plain,(
    ! [B_66] :
      ( r1_tarski(u1_struct_0(B_66),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_3')))
      | ~ m1_pre_topc(B_66,k1_tsep_1('#skF_1','#skF_3','#skF_3'))
      | ~ m1_pre_topc(B_66,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_472])).

tff(c_512,plain,(
    ! [B_66] :
      ( r1_tarski(u1_struct_0(B_66),u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_3')))
      | ~ m1_pre_topc(B_66,k1_tsep_1('#skF_1','#skF_4','#skF_3'))
      | ~ m1_pre_topc(B_66,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_510,c_510,c_485])).

tff(c_1812,plain,(
    ! [B_66] :
      ( r1_tarski(u1_struct_0(B_66),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_66,k1_tsep_1('#skF_1','#skF_4','#skF_3'))
      | ~ m1_pre_topc(B_66,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_637,c_512])).

tff(c_4422,plain,(
    ! [A_247] :
      ( r1_tarski(u1_struct_0(k1_tsep_1(A_247,'#skF_2','#skF_4')),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_4'),k1_tsep_1('#skF_1','#skF_4','#skF_3'))
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_4'),'#skF_1')
      | ~ m1_pre_topc('#skF_4',A_247)
      | ~ m1_pre_topc('#skF_2',A_247)
      | ~ l1_pre_topc(A_247)
      | v2_struct_0(A_247) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4348,c_1812])).

tff(c_4524,plain,(
    ! [A_247] :
      ( r1_tarski(u1_struct_0(k1_tsep_1(A_247,'#skF_2','#skF_4')),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_4'),k1_tsep_1('#skF_1','#skF_4','#skF_3'))
      | ~ m1_pre_topc('#skF_4',A_247)
      | ~ m1_pre_topc('#skF_2',A_247)
      | ~ l1_pre_topc(A_247)
      | v2_struct_0(A_247) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_4422])).

tff(c_6452,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_4'),k1_tsep_1('#skF_1','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_4524])).

tff(c_6461,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_674,c_6452])).

tff(c_6474,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_32,c_30,c_28,c_6461])).

tff(c_6476,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_34,c_6474])).

tff(c_6478,plain,(
    m1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_4'),k1_tsep_1('#skF_1','#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_4524])).

tff(c_1813,plain,(
    ! [B_172] :
      ( r1_tarski(u1_struct_0(B_172),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_172,k1_tsep_1('#skF_1','#skF_4','#skF_3'))
      | ~ m1_pre_topc(B_172,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_637,c_512])).

tff(c_24,plain,(
    ! [B_66,C_68,A_62] :
      ( m1_pre_topc(B_66,C_68)
      | ~ r1_tarski(u1_struct_0(B_66),u1_struct_0(C_68))
      | ~ m1_pre_topc(C_68,A_62)
      | ~ m1_pre_topc(B_66,A_62)
      | ~ l1_pre_topc(A_62)
      | ~ v2_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_2185,plain,(
    ! [B_184,A_185] :
      ( m1_pre_topc(B_184,'#skF_3')
      | ~ m1_pre_topc('#skF_3',A_185)
      | ~ m1_pre_topc(B_184,A_185)
      | ~ l1_pre_topc(A_185)
      | ~ v2_pre_topc(A_185)
      | ~ m1_pre_topc(B_184,k1_tsep_1('#skF_1','#skF_4','#skF_3'))
      | ~ m1_pre_topc(B_184,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_1813,c_24])).

tff(c_2192,plain,(
    ! [B_184] :
      ( m1_pre_topc(B_184,'#skF_3')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ m1_pre_topc(B_184,k1_tsep_1('#skF_1','#skF_4','#skF_3'))
      | ~ m1_pre_topc(B_184,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_36,c_2185])).

tff(c_2200,plain,(
    ! [B_184] :
      ( m1_pre_topc(B_184,'#skF_3')
      | ~ m1_pre_topc(B_184,k1_tsep_1('#skF_1','#skF_4','#skF_3'))
      | ~ m1_pre_topc(B_184,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_2192])).

tff(c_6491,plain,
    ( m1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_4'),'#skF_3')
    | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_4'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_6478,c_2200])).

tff(c_6520,plain,(
    m1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_6491])).

tff(c_6522,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_6520])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:52:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.44/2.79  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.66/2.81  
% 8.66/2.81  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.66/2.81  %$ r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k1_tsep_1 > k2_xboole_0 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.66/2.81  
% 8.66/2.81  %Foreground sorts:
% 8.66/2.81  
% 8.66/2.81  
% 8.66/2.81  %Background operators:
% 8.66/2.81  
% 8.66/2.81  
% 8.66/2.81  %Foreground operators:
% 8.66/2.81  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.66/2.81  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 8.66/2.81  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 8.66/2.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.66/2.81  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 8.66/2.81  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.66/2.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.66/2.81  tff('#skF_2', type, '#skF_2': $i).
% 8.66/2.81  tff('#skF_3', type, '#skF_3': $i).
% 8.66/2.81  tff('#skF_1', type, '#skF_1': $i).
% 8.66/2.81  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 8.66/2.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.66/2.81  tff('#skF_4', type, '#skF_4': $i).
% 8.66/2.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.66/2.81  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 8.66/2.81  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.66/2.81  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.66/2.81  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.66/2.81  
% 8.66/2.83  tff(f_201, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => ((m1_pre_topc(B, C) & m1_pre_topc(D, C)) => m1_pre_topc(k1_tsep_1(A, B, D), C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tmap_1)).
% 8.66/2.83  tff(f_80, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => ((~v2_struct_0(k1_tsep_1(A, B, C)) & v1_pre_topc(k1_tsep_1(A, B, C))) & m1_pre_topc(k1_tsep_1(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 8.66/2.83  tff(f_118, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (k1_tsep_1(A, B, B) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_tmap_1)).
% 8.66/2.83  tff(f_103, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (m1_pre_topc(B, C) <=> (k1_tsep_1(A, B, C) = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_tsep_1)).
% 8.66/2.83  tff(f_155, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: ((~v2_struct_0(E) & m1_pre_topc(E, A)) => ((m1_pre_topc(B, C) & m1_pre_topc(D, E)) => m1_pre_topc(k1_tsep_1(A, B, D), k1_tsep_1(A, C, E))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_tmap_1)).
% 8.66/2.83  tff(f_58, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (((~v2_struct_0(D) & v1_pre_topc(D)) & m1_pre_topc(D, A)) => ((D = k1_tsep_1(A, B, C)) <=> (u1_struct_0(D) = k2_xboole_0(u1_struct_0(B), u1_struct_0(C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tsep_1)).
% 8.66/2.83  tff(f_169, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 8.66/2.83  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 8.66/2.83  tff(c_26, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_201])).
% 8.66/2.83  tff(c_48, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_201])).
% 8.66/2.83  tff(c_42, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_201])).
% 8.66/2.83  tff(c_34, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_201])).
% 8.66/2.83  tff(c_44, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_201])).
% 8.66/2.83  tff(c_40, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_201])).
% 8.66/2.83  tff(c_32, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_201])).
% 8.66/2.83  tff(c_8, plain, (![A_18, B_19, C_20]: (m1_pre_topc(k1_tsep_1(A_18, B_19, C_20), A_18) | ~m1_pre_topc(C_20, A_18) | v2_struct_0(C_20) | ~m1_pre_topc(B_19, A_18) | v2_struct_0(B_19) | ~l1_pre_topc(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.66/2.83  tff(c_46, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_201])).
% 8.66/2.83  tff(c_36, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_201])).
% 8.66/2.83  tff(c_38, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_201])).
% 8.66/2.83  tff(c_131, plain, (![A_103, B_104]: (k1_tsep_1(A_103, B_104, B_104)=g1_pre_topc(u1_struct_0(B_104), u1_pre_topc(B_104)) | ~m1_pre_topc(B_104, A_103) | v2_struct_0(B_104) | ~l1_pre_topc(A_103) | ~v2_pre_topc(A_103) | v2_struct_0(A_103))), inference(cnfTransformation, [status(thm)], [f_118])).
% 8.66/2.83  tff(c_143, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=k1_tsep_1('#skF_1', '#skF_3', '#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_131])).
% 8.66/2.83  tff(c_159, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=k1_tsep_1('#skF_1', '#skF_3', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_143])).
% 8.66/2.83  tff(c_160, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=k1_tsep_1('#skF_1', '#skF_3', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_48, c_38, c_159])).
% 8.66/2.83  tff(c_173, plain, (![B_105, C_106, A_107]: (m1_pre_topc(B_105, C_106) | k1_tsep_1(A_107, B_105, C_106)!=g1_pre_topc(u1_struct_0(C_106), u1_pre_topc(C_106)) | ~m1_pre_topc(C_106, A_107) | v2_struct_0(C_106) | ~m1_pre_topc(B_105, A_107) | v2_struct_0(B_105) | ~l1_pre_topc(A_107) | ~v2_pre_topc(A_107) | v2_struct_0(A_107))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.66/2.83  tff(c_175, plain, (![B_105, A_107]: (m1_pre_topc(B_105, '#skF_3') | k1_tsep_1(A_107, B_105, '#skF_3')!=k1_tsep_1('#skF_1', '#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', A_107) | v2_struct_0('#skF_3') | ~m1_pre_topc(B_105, A_107) | v2_struct_0(B_105) | ~l1_pre_topc(A_107) | ~v2_pre_topc(A_107) | v2_struct_0(A_107))), inference(superposition, [status(thm), theory('equality')], [c_160, c_173])).
% 8.66/2.83  tff(c_183, plain, (![B_108, A_109]: (m1_pre_topc(B_108, '#skF_3') | k1_tsep_1(A_109, B_108, '#skF_3')!=k1_tsep_1('#skF_1', '#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', A_109) | ~m1_pre_topc(B_108, A_109) | v2_struct_0(B_108) | ~l1_pre_topc(A_109) | ~v2_pre_topc(A_109) | v2_struct_0(A_109))), inference(negUnitSimplification, [status(thm)], [c_38, c_175])).
% 8.66/2.83  tff(c_185, plain, (![B_108]: (m1_pre_topc(B_108, '#skF_3') | k1_tsep_1('#skF_1', B_108, '#skF_3')!=k1_tsep_1('#skF_1', '#skF_3', '#skF_3') | ~m1_pre_topc(B_108, '#skF_1') | v2_struct_0(B_108) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_183])).
% 8.66/2.83  tff(c_188, plain, (![B_108]: (m1_pre_topc(B_108, '#skF_3') | k1_tsep_1('#skF_1', B_108, '#skF_3')!=k1_tsep_1('#skF_1', '#skF_3', '#skF_3') | ~m1_pre_topc(B_108, '#skF_1') | v2_struct_0(B_108) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_185])).
% 8.66/2.83  tff(c_190, plain, (![B_110]: (m1_pre_topc(B_110, '#skF_3') | k1_tsep_1('#skF_1', B_110, '#skF_3')!=k1_tsep_1('#skF_1', '#skF_3', '#skF_3') | ~m1_pre_topc(B_110, '#skF_1') | v2_struct_0(B_110))), inference(negUnitSimplification, [status(thm)], [c_48, c_188])).
% 8.66/2.83  tff(c_208, plain, (k1_tsep_1('#skF_1', k1_tsep_1('#skF_1', '#skF_2', '#skF_4'), '#skF_3')!=k1_tsep_1('#skF_1', '#skF_3', '#skF_3') | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_4'), '#skF_1') | v2_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_190, c_26])).
% 8.66/2.83  tff(c_209, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_4'), '#skF_1')), inference(splitLeft, [status(thm)], [c_208])).
% 8.66/2.83  tff(c_246, plain, (~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_8, c_209])).
% 8.66/2.83  tff(c_249, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_32, c_246])).
% 8.66/2.83  tff(c_251, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_42, c_34, c_249])).
% 8.66/2.83  tff(c_253, plain, (m1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_4'), '#skF_1')), inference(splitRight, [status(thm)], [c_208])).
% 8.66/2.83  tff(c_30, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_201])).
% 8.66/2.83  tff(c_28, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_201])).
% 8.66/2.83  tff(c_329, plain, (![A_117, B_118, C_119]: (k1_tsep_1(A_117, B_118, C_119)=g1_pre_topc(u1_struct_0(C_119), u1_pre_topc(C_119)) | ~m1_pre_topc(B_118, C_119) | ~m1_pre_topc(C_119, A_117) | v2_struct_0(C_119) | ~m1_pre_topc(B_118, A_117) | v2_struct_0(B_118) | ~l1_pre_topc(A_117) | ~v2_pre_topc(A_117) | v2_struct_0(A_117))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.66/2.83  tff(c_339, plain, (![A_117]: (k1_tsep_1(A_117, '#skF_4', '#skF_3')=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')) | ~m1_pre_topc('#skF_3', A_117) | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', A_117) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_117) | ~v2_pre_topc(A_117) | v2_struct_0(A_117))), inference(resolution, [status(thm)], [c_28, c_329])).
% 8.66/2.83  tff(c_359, plain, (![A_117]: (k1_tsep_1(A_117, '#skF_4', '#skF_3')=k1_tsep_1('#skF_1', '#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', A_117) | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', A_117) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_117) | ~v2_pre_topc(A_117) | v2_struct_0(A_117))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_339])).
% 8.66/2.83  tff(c_495, plain, (![A_128]: (k1_tsep_1(A_128, '#skF_4', '#skF_3')=k1_tsep_1('#skF_1', '#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', A_128) | ~m1_pre_topc('#skF_4', A_128) | ~l1_pre_topc(A_128) | ~v2_pre_topc(A_128) | v2_struct_0(A_128))), inference(negUnitSimplification, [status(thm)], [c_34, c_38, c_359])).
% 8.66/2.83  tff(c_502, plain, (k1_tsep_1('#skF_1', '#skF_3', '#skF_3')=k1_tsep_1('#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_495])).
% 8.66/2.83  tff(c_509, plain, (k1_tsep_1('#skF_1', '#skF_3', '#skF_3')=k1_tsep_1('#skF_1', '#skF_4', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_32, c_502])).
% 8.66/2.83  tff(c_510, plain, (k1_tsep_1('#skF_1', '#skF_3', '#skF_3')=k1_tsep_1('#skF_1', '#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_48, c_509])).
% 8.66/2.83  tff(c_641, plain, (![C_132, E_133, D_136, B_134, A_135]: (m1_pre_topc(k1_tsep_1(A_135, B_134, D_136), k1_tsep_1(A_135, C_132, E_133)) | ~m1_pre_topc(D_136, E_133) | ~m1_pre_topc(B_134, C_132) | ~m1_pre_topc(E_133, A_135) | v2_struct_0(E_133) | ~m1_pre_topc(D_136, A_135) | v2_struct_0(D_136) | ~m1_pre_topc(C_132, A_135) | v2_struct_0(C_132) | ~m1_pre_topc(B_134, A_135) | v2_struct_0(B_134) | ~l1_pre_topc(A_135) | ~v2_pre_topc(A_135) | v2_struct_0(A_135))), inference(cnfTransformation, [status(thm)], [f_155])).
% 8.66/2.83  tff(c_659, plain, (![B_134, D_136]: (m1_pre_topc(k1_tsep_1('#skF_1', B_134, D_136), k1_tsep_1('#skF_1', '#skF_4', '#skF_3')) | ~m1_pre_topc(D_136, '#skF_3') | ~m1_pre_topc(B_134, '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc(D_136, '#skF_1') | v2_struct_0(D_136) | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_134, '#skF_1') | v2_struct_0(B_134) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_510, c_641])).
% 8.66/2.83  tff(c_673, plain, (![B_134, D_136]: (m1_pre_topc(k1_tsep_1('#skF_1', B_134, D_136), k1_tsep_1('#skF_1', '#skF_4', '#skF_3')) | ~m1_pre_topc(D_136, '#skF_3') | ~m1_pre_topc(B_134, '#skF_3') | ~m1_pre_topc(D_136, '#skF_1') | v2_struct_0(D_136) | v2_struct_0('#skF_3') | ~m1_pre_topc(B_134, '#skF_1') | v2_struct_0(B_134) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_36, c_36, c_659])).
% 8.66/2.83  tff(c_674, plain, (![B_134, D_136]: (m1_pre_topc(k1_tsep_1('#skF_1', B_134, D_136), k1_tsep_1('#skF_1', '#skF_4', '#skF_3')) | ~m1_pre_topc(D_136, '#skF_3') | ~m1_pre_topc(B_134, '#skF_3') | ~m1_pre_topc(D_136, '#skF_1') | v2_struct_0(D_136) | ~m1_pre_topc(B_134, '#skF_1') | v2_struct_0(B_134))), inference(negUnitSimplification, [status(thm)], [c_48, c_38, c_673])).
% 8.66/2.83  tff(c_10, plain, (![A_18, B_19, C_20]: (v1_pre_topc(k1_tsep_1(A_18, B_19, C_20)) | ~m1_pre_topc(C_20, A_18) | v2_struct_0(C_20) | ~m1_pre_topc(B_19, A_18) | v2_struct_0(B_19) | ~l1_pre_topc(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.66/2.83  tff(c_545, plain, (![A_129, B_130, C_131]: (u1_struct_0(k1_tsep_1(A_129, B_130, C_131))=k2_xboole_0(u1_struct_0(B_130), u1_struct_0(C_131)) | ~m1_pre_topc(k1_tsep_1(A_129, B_130, C_131), A_129) | ~v1_pre_topc(k1_tsep_1(A_129, B_130, C_131)) | v2_struct_0(k1_tsep_1(A_129, B_130, C_131)) | ~m1_pre_topc(C_131, A_129) | v2_struct_0(C_131) | ~m1_pre_topc(B_130, A_129) | v2_struct_0(B_130) | ~l1_pre_topc(A_129) | v2_struct_0(A_129))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.66/2.83  tff(c_549, plain, (k2_xboole_0(u1_struct_0('#skF_2'), u1_struct_0('#skF_4'))=u1_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_4')) | ~v1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_4')) | v2_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_253, c_545])).
% 8.66/2.83  tff(c_557, plain, (k2_xboole_0(u1_struct_0('#skF_2'), u1_struct_0('#skF_4'))=u1_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_4')) | ~v1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_4')) | v2_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_4')) | v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_32, c_549])).
% 8.66/2.83  tff(c_558, plain, (k2_xboole_0(u1_struct_0('#skF_2'), u1_struct_0('#skF_4'))=u1_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_4')) | ~v1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_4')) | v2_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_48, c_42, c_34, c_557])).
% 8.66/2.83  tff(c_1962, plain, (~v1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_558])).
% 8.66/2.83  tff(c_1965, plain, (~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_10, c_1962])).
% 8.66/2.83  tff(c_1968, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_32, c_1965])).
% 8.66/2.83  tff(c_1970, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_42, c_34, c_1968])).
% 8.66/2.83  tff(c_1971, plain, (v2_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_4')) | k2_xboole_0(u1_struct_0('#skF_2'), u1_struct_0('#skF_4'))=u1_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_558])).
% 8.66/2.83  tff(c_2002, plain, (k2_xboole_0(u1_struct_0('#skF_2'), u1_struct_0('#skF_4'))=u1_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_1971])).
% 8.66/2.83  tff(c_2028, plain, (![A_181, B_182, C_183]: (u1_struct_0(k1_tsep_1(A_181, B_182, C_183))=k2_xboole_0(u1_struct_0(B_182), u1_struct_0(C_183)) | ~v1_pre_topc(k1_tsep_1(A_181, B_182, C_183)) | v2_struct_0(k1_tsep_1(A_181, B_182, C_183)) | ~m1_pre_topc(C_183, A_181) | v2_struct_0(C_183) | ~m1_pre_topc(B_182, A_181) | v2_struct_0(B_182) | ~l1_pre_topc(A_181) | v2_struct_0(A_181))), inference(resolution, [status(thm)], [c_8, c_545])).
% 8.66/2.83  tff(c_12, plain, (![A_18, B_19, C_20]: (~v2_struct_0(k1_tsep_1(A_18, B_19, C_20)) | ~m1_pre_topc(C_20, A_18) | v2_struct_0(C_20) | ~m1_pre_topc(B_19, A_18) | v2_struct_0(B_19) | ~l1_pre_topc(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.66/2.83  tff(c_3630, plain, (![A_235, B_236, C_237]: (u1_struct_0(k1_tsep_1(A_235, B_236, C_237))=k2_xboole_0(u1_struct_0(B_236), u1_struct_0(C_237)) | ~v1_pre_topc(k1_tsep_1(A_235, B_236, C_237)) | ~m1_pre_topc(C_237, A_235) | v2_struct_0(C_237) | ~m1_pre_topc(B_236, A_235) | v2_struct_0(B_236) | ~l1_pre_topc(A_235) | v2_struct_0(A_235))), inference(resolution, [status(thm)], [c_2028, c_12])).
% 8.66/2.83  tff(c_3664, plain, (![A_238, B_239, C_240]: (u1_struct_0(k1_tsep_1(A_238, B_239, C_240))=k2_xboole_0(u1_struct_0(B_239), u1_struct_0(C_240)) | ~m1_pre_topc(C_240, A_238) | v2_struct_0(C_240) | ~m1_pre_topc(B_239, A_238) | v2_struct_0(B_239) | ~l1_pre_topc(A_238) | v2_struct_0(A_238))), inference(resolution, [status(thm)], [c_10, c_3630])).
% 8.66/2.83  tff(c_3798, plain, (![A_238]: (u1_struct_0(k1_tsep_1(A_238, '#skF_2', '#skF_4'))=u1_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_4')) | ~m1_pre_topc('#skF_4', A_238) | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_2', A_238) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_238) | v2_struct_0(A_238))), inference(superposition, [status(thm), theory('equality')], [c_2002, c_3664])).
% 8.66/2.83  tff(c_4348, plain, (![A_247]: (u1_struct_0(k1_tsep_1(A_247, '#skF_2', '#skF_4'))=u1_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_4')) | ~m1_pre_topc('#skF_4', A_247) | ~m1_pre_topc('#skF_2', A_247) | ~l1_pre_topc(A_247) | v2_struct_0(A_247))), inference(negUnitSimplification, [status(thm)], [c_42, c_34, c_3798])).
% 8.66/2.83  tff(c_345, plain, (![A_117]: (k1_tsep_1(A_117, '#skF_2', '#skF_3')=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')) | ~m1_pre_topc('#skF_3', A_117) | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', A_117) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_117) | ~v2_pre_topc(A_117) | v2_struct_0(A_117))), inference(resolution, [status(thm)], [c_30, c_329])).
% 8.66/2.83  tff(c_368, plain, (![A_117]: (k1_tsep_1(A_117, '#skF_2', '#skF_3')=k1_tsep_1('#skF_1', '#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', A_117) | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', A_117) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_117) | ~v2_pre_topc(A_117) | v2_struct_0(A_117))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_345])).
% 8.66/2.83  tff(c_411, plain, (![A_122]: (k1_tsep_1(A_122, '#skF_2', '#skF_3')=k1_tsep_1('#skF_1', '#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', A_122) | ~m1_pre_topc('#skF_2', A_122) | ~l1_pre_topc(A_122) | ~v2_pre_topc(A_122) | v2_struct_0(A_122))), inference(negUnitSimplification, [status(thm)], [c_42, c_38, c_368])).
% 8.66/2.83  tff(c_418, plain, (k1_tsep_1('#skF_1', '#skF_2', '#skF_3')=k1_tsep_1('#skF_1', '#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_411])).
% 8.66/2.83  tff(c_428, plain, (k1_tsep_1('#skF_1', '#skF_2', '#skF_3')=k1_tsep_1('#skF_1', '#skF_3', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_36, c_418])).
% 8.66/2.83  tff(c_429, plain, (k1_tsep_1('#skF_1', '#skF_2', '#skF_3')=k1_tsep_1('#skF_1', '#skF_3', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_48, c_428])).
% 8.66/2.83  tff(c_451, plain, (~v2_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_429, c_12])).
% 8.66/2.83  tff(c_461, plain, (~v2_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_3')) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_36, c_451])).
% 8.66/2.83  tff(c_462, plain, (~v2_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_48, c_42, c_38, c_461])).
% 8.66/2.83  tff(c_515, plain, (~v2_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_510, c_462])).
% 8.66/2.83  tff(c_517, plain, (k1_tsep_1('#skF_1', '#skF_2', '#skF_3')=k1_tsep_1('#skF_1', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_510, c_429])).
% 8.66/2.83  tff(c_448, plain, (v1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_429, c_10])).
% 8.66/2.83  tff(c_458, plain, (v1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_3')) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_36, c_448])).
% 8.66/2.83  tff(c_459, plain, (v1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_48, c_42, c_38, c_458])).
% 8.66/2.83  tff(c_516, plain, (v1_pre_topc(k1_tsep_1('#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_510, c_459])).
% 8.66/2.83  tff(c_445, plain, (m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_3'), '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_429, c_8])).
% 8.66/2.83  tff(c_455, plain, (m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_3'), '#skF_1') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_36, c_445])).
% 8.66/2.83  tff(c_456, plain, (m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_3'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_48, c_42, c_38, c_455])).
% 8.66/2.83  tff(c_514, plain, (m1_pre_topc(k1_tsep_1('#skF_1', '#skF_4', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_510, c_456])).
% 8.66/2.83  tff(c_6, plain, (![A_3, B_11, C_15]: (u1_struct_0(k1_tsep_1(A_3, B_11, C_15))=k2_xboole_0(u1_struct_0(B_11), u1_struct_0(C_15)) | ~m1_pre_topc(k1_tsep_1(A_3, B_11, C_15), A_3) | ~v1_pre_topc(k1_tsep_1(A_3, B_11, C_15)) | v2_struct_0(k1_tsep_1(A_3, B_11, C_15)) | ~m1_pre_topc(C_15, A_3) | v2_struct_0(C_15) | ~m1_pre_topc(B_11, A_3) | v2_struct_0(B_11) | ~l1_pre_topc(A_3) | v2_struct_0(A_3))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.66/2.83  tff(c_592, plain, (k2_xboole_0(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))=u1_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_4', '#skF_3'), '#skF_1') | ~v1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_3')) | v2_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_517, c_6])).
% 8.66/2.83  tff(c_605, plain, (k2_xboole_0(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))=u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_3')) | v2_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_3')) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_36, c_517, c_516, c_517, c_514, c_517, c_592])).
% 8.66/2.83  tff(c_606, plain, (k2_xboole_0(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))=u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_48, c_42, c_38, c_515, c_605])).
% 8.66/2.83  tff(c_51, plain, (![B_85, C_86, A_87]: (r1_tarski(u1_struct_0(B_85), u1_struct_0(C_86)) | ~m1_pre_topc(B_85, C_86) | ~m1_pre_topc(C_86, A_87) | ~m1_pre_topc(B_85, A_87) | ~l1_pre_topc(A_87) | ~v2_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_169])).
% 8.66/2.83  tff(c_61, plain, (![B_85]: (r1_tarski(u1_struct_0(B_85), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_85, '#skF_3') | ~m1_pre_topc(B_85, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_51])).
% 8.66/2.83  tff(c_82, plain, (![B_92]: (r1_tarski(u1_struct_0(B_92), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_92, '#skF_3') | ~m1_pre_topc(B_92, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_61])).
% 8.66/2.83  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(A_1, B_2)=B_2 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.66/2.83  tff(c_89, plain, (![B_92]: (k2_xboole_0(u1_struct_0(B_92), u1_struct_0('#skF_3'))=u1_struct_0('#skF_3') | ~m1_pre_topc(B_92, '#skF_3') | ~m1_pre_topc(B_92, '#skF_1'))), inference(resolution, [status(thm)], [c_82, c_2])).
% 8.66/2.83  tff(c_629, plain, (u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_3'))=u1_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_606, c_89])).
% 8.66/2.83  tff(c_637, plain, (u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_3'))=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_30, c_629])).
% 8.66/2.83  tff(c_22, plain, (![B_66, C_68, A_62]: (r1_tarski(u1_struct_0(B_66), u1_struct_0(C_68)) | ~m1_pre_topc(B_66, C_68) | ~m1_pre_topc(C_68, A_62) | ~m1_pre_topc(B_66, A_62) | ~l1_pre_topc(A_62) | ~v2_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_169])).
% 8.66/2.83  tff(c_472, plain, (![B_66]: (r1_tarski(u1_struct_0(B_66), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_3'))) | ~m1_pre_topc(B_66, k1_tsep_1('#skF_1', '#skF_3', '#skF_3')) | ~m1_pre_topc(B_66, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_456, c_22])).
% 8.66/2.83  tff(c_485, plain, (![B_66]: (r1_tarski(u1_struct_0(B_66), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_3'))) | ~m1_pre_topc(B_66, k1_tsep_1('#skF_1', '#skF_3', '#skF_3')) | ~m1_pre_topc(B_66, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_472])).
% 8.66/2.83  tff(c_512, plain, (![B_66]: (r1_tarski(u1_struct_0(B_66), u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_3'))) | ~m1_pre_topc(B_66, k1_tsep_1('#skF_1', '#skF_4', '#skF_3')) | ~m1_pre_topc(B_66, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_510, c_510, c_485])).
% 8.66/2.83  tff(c_1812, plain, (![B_66]: (r1_tarski(u1_struct_0(B_66), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_66, k1_tsep_1('#skF_1', '#skF_4', '#skF_3')) | ~m1_pre_topc(B_66, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_637, c_512])).
% 8.66/2.83  tff(c_4422, plain, (![A_247]: (r1_tarski(u1_struct_0(k1_tsep_1(A_247, '#skF_2', '#skF_4')), u1_struct_0('#skF_3')) | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_4'), k1_tsep_1('#skF_1', '#skF_4', '#skF_3')) | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_4'), '#skF_1') | ~m1_pre_topc('#skF_4', A_247) | ~m1_pre_topc('#skF_2', A_247) | ~l1_pre_topc(A_247) | v2_struct_0(A_247))), inference(superposition, [status(thm), theory('equality')], [c_4348, c_1812])).
% 8.66/2.83  tff(c_4524, plain, (![A_247]: (r1_tarski(u1_struct_0(k1_tsep_1(A_247, '#skF_2', '#skF_4')), u1_struct_0('#skF_3')) | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_4'), k1_tsep_1('#skF_1', '#skF_4', '#skF_3')) | ~m1_pre_topc('#skF_4', A_247) | ~m1_pre_topc('#skF_2', A_247) | ~l1_pre_topc(A_247) | v2_struct_0(A_247))), inference(demodulation, [status(thm), theory('equality')], [c_253, c_4422])).
% 8.66/2.83  tff(c_6452, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_4'), k1_tsep_1('#skF_1', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_4524])).
% 8.66/2.83  tff(c_6461, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_674, c_6452])).
% 8.66/2.83  tff(c_6474, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_32, c_30, c_28, c_6461])).
% 8.66/2.83  tff(c_6476, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_34, c_6474])).
% 8.66/2.83  tff(c_6478, plain, (m1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_4'), k1_tsep_1('#skF_1', '#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_4524])).
% 8.66/2.83  tff(c_1813, plain, (![B_172]: (r1_tarski(u1_struct_0(B_172), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_172, k1_tsep_1('#skF_1', '#skF_4', '#skF_3')) | ~m1_pre_topc(B_172, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_637, c_512])).
% 8.66/2.83  tff(c_24, plain, (![B_66, C_68, A_62]: (m1_pre_topc(B_66, C_68) | ~r1_tarski(u1_struct_0(B_66), u1_struct_0(C_68)) | ~m1_pre_topc(C_68, A_62) | ~m1_pre_topc(B_66, A_62) | ~l1_pre_topc(A_62) | ~v2_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_169])).
% 8.66/2.83  tff(c_2185, plain, (![B_184, A_185]: (m1_pre_topc(B_184, '#skF_3') | ~m1_pre_topc('#skF_3', A_185) | ~m1_pre_topc(B_184, A_185) | ~l1_pre_topc(A_185) | ~v2_pre_topc(A_185) | ~m1_pre_topc(B_184, k1_tsep_1('#skF_1', '#skF_4', '#skF_3')) | ~m1_pre_topc(B_184, '#skF_1'))), inference(resolution, [status(thm)], [c_1813, c_24])).
% 8.66/2.83  tff(c_2192, plain, (![B_184]: (m1_pre_topc(B_184, '#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_pre_topc(B_184, k1_tsep_1('#skF_1', '#skF_4', '#skF_3')) | ~m1_pre_topc(B_184, '#skF_1'))), inference(resolution, [status(thm)], [c_36, c_2185])).
% 8.66/2.83  tff(c_2200, plain, (![B_184]: (m1_pre_topc(B_184, '#skF_3') | ~m1_pre_topc(B_184, k1_tsep_1('#skF_1', '#skF_4', '#skF_3')) | ~m1_pre_topc(B_184, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_2192])).
% 8.66/2.83  tff(c_6491, plain, (m1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_4'), '#skF_3') | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_4'), '#skF_1')), inference(resolution, [status(thm)], [c_6478, c_2200])).
% 8.66/2.83  tff(c_6520, plain, (m1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_253, c_6491])).
% 8.66/2.83  tff(c_6522, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_6520])).
% 8.66/2.83  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.66/2.83  
% 8.66/2.83  Inference rules
% 8.66/2.83  ----------------------
% 8.66/2.83  #Ref     : 0
% 8.66/2.83  #Sup     : 1436
% 8.66/2.83  #Fact    : 0
% 8.66/2.83  #Define  : 0
% 8.66/2.83  #Split   : 52
% 8.66/2.83  #Chain   : 0
% 8.66/2.83  #Close   : 0
% 8.66/2.83  
% 8.66/2.83  Ordering : KBO
% 8.66/2.83  
% 8.66/2.83  Simplification rules
% 8.66/2.83  ----------------------
% 8.66/2.83  #Subsume      : 347
% 8.66/2.83  #Demod        : 1795
% 8.66/2.83  #Tautology    : 244
% 8.66/2.83  #SimpNegUnit  : 659
% 8.66/2.83  #BackRed      : 13
% 8.66/2.83  
% 8.66/2.83  #Partial instantiations: 0
% 8.66/2.83  #Strategies tried      : 1
% 8.66/2.83  
% 8.66/2.83  Timing (in seconds)
% 8.66/2.83  ----------------------
% 8.66/2.84  Preprocessing        : 0.32
% 8.66/2.84  Parsing              : 0.17
% 8.66/2.84  CNF conversion       : 0.03
% 8.66/2.84  Main loop            : 1.72
% 8.66/2.84  Inferencing          : 0.49
% 8.66/2.84  Reduction            : 0.59
% 8.66/2.84  Demodulation         : 0.42
% 8.66/2.84  BG Simplification    : 0.07
% 8.66/2.84  Subsumption          : 0.48
% 8.66/2.84  Abstraction          : 0.10
% 8.66/2.84  MUC search           : 0.00
% 8.66/2.84  Cooper               : 0.00
% 8.66/2.84  Total                : 2.09
% 8.66/2.84  Index Insertion      : 0.00
% 8.66/2.84  Index Deletion       : 0.00
% 8.66/2.84  Index Matching       : 0.00
% 8.66/2.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
