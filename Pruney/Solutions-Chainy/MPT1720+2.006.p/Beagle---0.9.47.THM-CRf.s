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
% DateTime   : Thu Dec  3 10:26:42 EST 2020

% Result     : Theorem 7.59s
% Output     : CNFRefutation 7.90s
% Verified   : 
% Statistics : Number of formulae       :  153 (1038 expanded)
%              Number of leaves         :   29 ( 396 expanded)
%              Depth                    :   22
%              Number of atoms          :  461 (5563 expanded)
%              Number of equality atoms :   40 ( 209 expanded)
%              Maximal formula depth    :   14 (   5 average)
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

tff(f_197,negated_conjecture,(
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

tff(f_64,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & m1_pre_topc(B,A)
        & ~ v2_struct_0(C)
        & m1_pre_topc(C,A) )
     => k1_tsep_1(A,B,C) = k1_tsep_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k1_tsep_1)).

tff(f_115,axiom,(
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

tff(f_165,axiom,(
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

tff(f_136,axiom,(
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
             => m1_pre_topc(B,k1_tsep_1(A,B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tsep_1)).

tff(f_40,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_151,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => k1_tsep_1(A,B,B) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tmap_1)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_xboole_1)).

tff(f_93,axiom,(
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

tff(c_50,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_48,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_40,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_44,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_36,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_4433,plain,(
    ! [A_304,C_305,B_306] :
      ( k1_tsep_1(A_304,C_305,B_306) = k1_tsep_1(A_304,B_306,C_305)
      | ~ m1_pre_topc(C_305,A_304)
      | v2_struct_0(C_305)
      | ~ m1_pre_topc(B_306,A_304)
      | v2_struct_0(B_306)
      | ~ l1_pre_topc(A_304)
      | v2_struct_0(A_304) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4445,plain,(
    ! [B_306] :
      ( k1_tsep_1('#skF_1',B_306,'#skF_4') = k1_tsep_1('#skF_1','#skF_4',B_306)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_306,'#skF_1')
      | v2_struct_0(B_306)
      | ~ l1_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_36,c_4433])).

tff(c_4470,plain,(
    ! [B_306] :
      ( k1_tsep_1('#skF_1',B_306,'#skF_4') = k1_tsep_1('#skF_1','#skF_4',B_306)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_306,'#skF_1')
      | v2_struct_0(B_306)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_4445])).

tff(c_4521,plain,(
    ! [B_308] :
      ( k1_tsep_1('#skF_1',B_308,'#skF_4') = k1_tsep_1('#skF_1','#skF_4',B_308)
      | ~ m1_pre_topc(B_308,'#skF_1')
      | v2_struct_0(B_308) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_38,c_4470])).

tff(c_4531,plain,
    ( k1_tsep_1('#skF_1','#skF_2','#skF_4') = k1_tsep_1('#skF_1','#skF_4','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_4521])).

tff(c_4545,plain,(
    k1_tsep_1('#skF_1','#skF_2','#skF_4') = k1_tsep_1('#skF_1','#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_4531])).

tff(c_16,plain,(
    ! [A_30,B_31,C_32] :
      ( m1_pre_topc(k1_tsep_1(A_30,B_31,C_32),A_30)
      | ~ m1_pre_topc(C_32,A_30)
      | v2_struct_0(C_32)
      | ~ m1_pre_topc(B_31,A_30)
      | v2_struct_0(B_31)
      | ~ l1_pre_topc(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_4556,plain,
    ( m1_pre_topc(k1_tsep_1('#skF_1','#skF_4','#skF_2'),'#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4545,c_16])).

tff(c_4569,plain,
    ( m1_pre_topc(k1_tsep_1('#skF_1','#skF_4','#skF_2'),'#skF_1')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_36,c_4556])).

tff(c_4570,plain,(
    m1_pre_topc(k1_tsep_1('#skF_1','#skF_4','#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_46,c_38,c_4569])).

tff(c_30,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_4549,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_4','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4545,c_30])).

tff(c_34,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_134,plain,(
    ! [B_85,C_86,A_87] :
      ( r1_tarski(u1_struct_0(B_85),u1_struct_0(C_86))
      | ~ m1_pre_topc(B_85,C_86)
      | ~ m1_pre_topc(C_86,A_87)
      | ~ m1_pre_topc(B_85,A_87)
      | ~ l1_pre_topc(A_87)
      | ~ v2_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_144,plain,(
    ! [B_85] :
      ( r1_tarski(u1_struct_0(B_85),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_85,'#skF_3')
      | ~ m1_pre_topc(B_85,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_40,c_134])).

tff(c_159,plain,(
    ! [B_85] :
      ( r1_tarski(u1_struct_0(B_85),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_85,'#skF_3')
      | ~ m1_pre_topc(B_85,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_144])).

tff(c_138,plain,(
    ! [B_85] :
      ( r1_tarski(u1_struct_0(B_85),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_85,'#skF_2')
      | ~ m1_pre_topc(B_85,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_44,c_134])).

tff(c_168,plain,(
    ! [B_89] :
      ( r1_tarski(u1_struct_0(B_89),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_89,'#skF_2')
      | ~ m1_pre_topc(B_89,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_138])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k2_xboole_0(A_1,B_2) = B_2
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_175,plain,(
    ! [B_89] :
      ( k2_xboole_0(u1_struct_0(B_89),u1_struct_0('#skF_2')) = u1_struct_0('#skF_2')
      | ~ m1_pre_topc(B_89,'#skF_2')
      | ~ m1_pre_topc(B_89,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_168,c_2])).

tff(c_2162,plain,(
    ! [B_202,A_203,C_204] :
      ( m1_pre_topc(B_202,k1_tsep_1(A_203,B_202,C_204))
      | ~ m1_pre_topc(C_204,A_203)
      | v2_struct_0(C_204)
      | ~ m1_pre_topc(B_202,A_203)
      | v2_struct_0(B_202)
      | ~ l1_pre_topc(A_203)
      | ~ v2_pre_topc(A_203)
      | v2_struct_0(A_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_53,plain,(
    ! [B_61,A_62] :
      ( l1_pre_topc(B_61)
      | ~ m1_pre_topc(B_61,A_62)
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_59,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_53])).

tff(c_74,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_59])).

tff(c_2044,plain,(
    ! [A_195,B_196] :
      ( k1_tsep_1(A_195,B_196,B_196) = g1_pre_topc(u1_struct_0(B_196),u1_pre_topc(B_196))
      | ~ m1_pre_topc(B_196,A_195)
      | v2_struct_0(B_196)
      | ~ l1_pre_topc(A_195)
      | ~ v2_pre_topc(A_195)
      | v2_struct_0(A_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_2052,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k1_tsep_1('#skF_1','#skF_2','#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_2044])).

tff(c_2070,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k1_tsep_1('#skF_1','#skF_2','#skF_2')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_2052])).

tff(c_2071,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k1_tsep_1('#skF_1','#skF_2','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_46,c_2070])).

tff(c_8,plain,(
    ! [B_11,A_9] :
      ( m1_pre_topc(B_11,A_9)
      | ~ m1_pre_topc(B_11,g1_pre_topc(u1_struct_0(A_9),u1_pre_topc(A_9)))
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2096,plain,(
    ! [B_11] :
      ( m1_pre_topc(B_11,'#skF_2')
      | ~ m1_pre_topc(B_11,k1_tsep_1('#skF_1','#skF_2','#skF_2'))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2071,c_8])).

tff(c_2100,plain,(
    ! [B_11] :
      ( m1_pre_topc(B_11,'#skF_2')
      | ~ m1_pre_topc(B_11,k1_tsep_1('#skF_1','#skF_2','#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2096])).

tff(c_2166,plain,
    ( m1_pre_topc('#skF_2','#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2162,c_2100])).

tff(c_2184,plain,
    ( m1_pre_topc('#skF_2','#skF_2')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_44,c_2166])).

tff(c_2185,plain,(
    m1_pre_topc('#skF_2','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_46,c_2184])).

tff(c_150,plain,(
    ! [B_85] :
      ( r1_tarski(u1_struct_0(B_85),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_85,'#skF_2')
      | ~ m1_pre_topc(B_85,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_138])).

tff(c_185,plain,(
    ! [B_91] :
      ( k2_xboole_0(u1_struct_0(B_91),u1_struct_0('#skF_2')) = u1_struct_0('#skF_2')
      | ~ m1_pre_topc(B_91,'#skF_2')
      | ~ m1_pre_topc(B_91,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_168,c_2])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(k2_xboole_0(A_3,C_5),k2_xboole_0(B_4,C_5))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_299,plain,(
    ! [B_103,B_104] :
      ( r1_tarski(u1_struct_0('#skF_2'),k2_xboole_0(B_103,u1_struct_0('#skF_2')))
      | ~ r1_tarski(u1_struct_0(B_104),B_103)
      | ~ m1_pre_topc(B_104,'#skF_2')
      | ~ m1_pre_topc(B_104,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_4])).

tff(c_307,plain,(
    ! [B_85] :
      ( r1_tarski(u1_struct_0('#skF_2'),k2_xboole_0(u1_struct_0('#skF_2'),u1_struct_0('#skF_2')))
      | ~ m1_pre_topc(B_85,'#skF_2')
      | ~ m1_pre_topc(B_85,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_150,c_299])).

tff(c_309,plain,(
    ! [B_85] :
      ( ~ m1_pre_topc(B_85,'#skF_2')
      | ~ m1_pre_topc(B_85,'#skF_1') ) ),
    inference(splitLeft,[status(thm)],[c_307])).

tff(c_2201,plain,(
    ~ m1_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_2185,c_309])).

tff(c_2214,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2201])).

tff(c_2215,plain,(
    r1_tarski(u1_struct_0('#skF_2'),k2_xboole_0(u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_307])).

tff(c_2229,plain,
    ( r1_tarski(u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_2','#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_2215])).

tff(c_2238,plain,
    ( r1_tarski(u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2229])).

tff(c_2239,plain,(
    ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2238])).

tff(c_3403,plain,(
    ! [B_266,A_267,C_268] :
      ( m1_pre_topc(B_266,k1_tsep_1(A_267,B_266,C_268))
      | ~ m1_pre_topc(C_268,A_267)
      | v2_struct_0(C_268)
      | ~ m1_pre_topc(B_266,A_267)
      | v2_struct_0(B_266)
      | ~ l1_pre_topc(A_267)
      | ~ v2_pre_topc(A_267)
      | v2_struct_0(A_267) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_3316,plain,(
    ! [A_259,B_260] :
      ( k1_tsep_1(A_259,B_260,B_260) = g1_pre_topc(u1_struct_0(B_260),u1_pre_topc(B_260))
      | ~ m1_pre_topc(B_260,A_259)
      | v2_struct_0(B_260)
      | ~ l1_pre_topc(A_259)
      | ~ v2_pre_topc(A_259)
      | v2_struct_0(A_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_3324,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k1_tsep_1('#skF_1','#skF_2','#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_3316])).

tff(c_3342,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k1_tsep_1('#skF_1','#skF_2','#skF_2')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_3324])).

tff(c_3343,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k1_tsep_1('#skF_1','#skF_2','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_46,c_3342])).

tff(c_3368,plain,(
    ! [B_11] :
      ( m1_pre_topc(B_11,'#skF_2')
      | ~ m1_pre_topc(B_11,k1_tsep_1('#skF_1','#skF_2','#skF_2'))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3343,c_8])).

tff(c_3372,plain,(
    ! [B_11] :
      ( m1_pre_topc(B_11,'#skF_2')
      | ~ m1_pre_topc(B_11,k1_tsep_1('#skF_1','#skF_2','#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_3368])).

tff(c_3407,plain,
    ( m1_pre_topc('#skF_2','#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_3403,c_3372])).

tff(c_3425,plain,
    ( m1_pre_topc('#skF_2','#skF_2')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_44,c_3407])).

tff(c_3427,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_46,c_2239,c_3425])).

tff(c_3429,plain,(
    m1_pre_topc('#skF_2','#skF_2') ),
    inference(splitRight,[status(thm)],[c_2238])).

tff(c_306,plain,(
    ! [B_85] :
      ( r1_tarski(u1_struct_0('#skF_2'),k2_xboole_0(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))
      | ~ m1_pre_topc(B_85,'#skF_2')
      | ~ m1_pre_topc(B_85,'#skF_3')
      | ~ m1_pre_topc(B_85,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_159,c_299])).

tff(c_3502,plain,(
    ! [B_269] :
      ( ~ m1_pre_topc(B_269,'#skF_2')
      | ~ m1_pre_topc(B_269,'#skF_3')
      | ~ m1_pre_topc(B_269,'#skF_1') ) ),
    inference(splitLeft,[status(thm)],[c_306])).

tff(c_3505,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_3429,c_3502])).

tff(c_3509,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_34,c_3505])).

tff(c_3510,plain,(
    r1_tarski(u1_struct_0('#skF_2'),k2_xboole_0(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_306])).

tff(c_3531,plain,(
    k2_xboole_0(u1_struct_0('#skF_2'),k2_xboole_0(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))) = k2_xboole_0(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_3510,c_2])).

tff(c_85,plain,(
    ! [A_65,C_66,B_67] :
      ( r1_tarski(k2_xboole_0(A_65,C_66),k2_xboole_0(B_67,C_66))
      | ~ r1_tarski(A_65,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_91,plain,(
    ! [A_70,C_71,B_72] :
      ( k2_xboole_0(k2_xboole_0(A_70,C_71),k2_xboole_0(B_72,C_71)) = k2_xboole_0(B_72,C_71)
      | ~ r1_tarski(A_70,B_72) ) ),
    inference(resolution,[status(thm)],[c_85,c_2])).

tff(c_106,plain,(
    ! [A_3,B_72,C_71,A_70] :
      ( r1_tarski(k2_xboole_0(A_3,k2_xboole_0(B_72,C_71)),k2_xboole_0(B_72,C_71))
      | ~ r1_tarski(A_3,k2_xboole_0(A_70,C_71))
      | ~ r1_tarski(A_70,B_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_4])).

tff(c_3965,plain,(
    ! [B_291] :
      ( r1_tarski(k2_xboole_0(u1_struct_0('#skF_2'),k2_xboole_0(B_291,u1_struct_0('#skF_2'))),k2_xboole_0(B_291,u1_struct_0('#skF_2')))
      | ~ r1_tarski(u1_struct_0('#skF_2'),B_291) ) ),
    inference(resolution,[status(thm)],[c_2215,c_106])).

tff(c_3988,plain,
    ( r1_tarski(k2_xboole_0(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')),k2_xboole_0(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))
    | ~ r1_tarski(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3531,c_3965])).

tff(c_4096,plain,(
    ~ r1_tarski(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_3988])).

tff(c_4099,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_159,c_4096])).

tff(c_4103,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_34,c_4099])).

tff(c_4105,plain,(
    r1_tarski(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_3988])).

tff(c_20,plain,(
    ! [A_30,B_31,C_32] :
      ( ~ v2_struct_0(k1_tsep_1(A_30,B_31,C_32))
      | ~ m1_pre_topc(C_32,A_30)
      | v2_struct_0(C_32)
      | ~ m1_pre_topc(B_31,A_30)
      | v2_struct_0(B_31)
      | ~ l1_pre_topc(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_4559,plain,
    ( ~ v2_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_2'))
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4545,c_20])).

tff(c_4572,plain,
    ( ~ v2_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_2'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_36,c_4559])).

tff(c_4573,plain,(
    ~ v2_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_46,c_38,c_4572])).

tff(c_18,plain,(
    ! [A_30,B_31,C_32] :
      ( v1_pre_topc(k1_tsep_1(A_30,B_31,C_32))
      | ~ m1_pre_topc(C_32,A_30)
      | v2_struct_0(C_32)
      | ~ m1_pre_topc(B_31,A_30)
      | v2_struct_0(B_31)
      | ~ l1_pre_topc(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_4562,plain,
    ( v1_pre_topc(k1_tsep_1('#skF_1','#skF_4','#skF_2'))
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4545,c_18])).

tff(c_4575,plain,
    ( v1_pre_topc(k1_tsep_1('#skF_1','#skF_4','#skF_2'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_36,c_4562])).

tff(c_4576,plain,(
    v1_pre_topc(k1_tsep_1('#skF_1','#skF_4','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_46,c_38,c_4575])).

tff(c_4792,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_4802,plain,
    ( k2_xboole_0(u1_struct_0('#skF_2'),u1_struct_0('#skF_4')) = u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_4'))
    | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_4','#skF_2'),'#skF_1')
    | ~ v1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_4'))
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4545,c_4792])).

tff(c_4820,plain,
    ( k2_xboole_0(u1_struct_0('#skF_2'),u1_struct_0('#skF_4')) = u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_2'))
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_2'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_36,c_4545,c_4576,c_4545,c_4570,c_4545,c_4802])).

tff(c_4821,plain,(
    k2_xboole_0(u1_struct_0('#skF_2'),u1_struct_0('#skF_4')) = u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_46,c_38,c_4573,c_4820])).

tff(c_32,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_4534,plain,
    ( k1_tsep_1('#skF_1','#skF_3','#skF_4') = k1_tsep_1('#skF_1','#skF_4','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_4521])).

tff(c_4548,plain,(
    k1_tsep_1('#skF_1','#skF_3','#skF_4') = k1_tsep_1('#skF_1','#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_4534])).

tff(c_4658,plain,
    ( ~ v2_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_3'))
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4548,c_20])).

tff(c_4671,plain,
    ( ~ v2_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_3'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_40,c_36,c_4658])).

tff(c_4672,plain,(
    ~ v2_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_42,c_38,c_4671])).

tff(c_4661,plain,
    ( v1_pre_topc(k1_tsep_1('#skF_1','#skF_4','#skF_3'))
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4548,c_18])).

tff(c_4674,plain,
    ( v1_pre_topc(k1_tsep_1('#skF_1','#skF_4','#skF_3'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_40,c_36,c_4661])).

tff(c_4675,plain,(
    v1_pre_topc(k1_tsep_1('#skF_1','#skF_4','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_42,c_38,c_4674])).

tff(c_4655,plain,
    ( m1_pre_topc(k1_tsep_1('#skF_1','#skF_4','#skF_3'),'#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4548,c_16])).

tff(c_4668,plain,
    ( m1_pre_topc(k1_tsep_1('#skF_1','#skF_4','#skF_3'),'#skF_1')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_40,c_36,c_4655])).

tff(c_4669,plain,(
    m1_pre_topc(k1_tsep_1('#skF_1','#skF_4','#skF_3'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_42,c_38,c_4668])).

tff(c_4796,plain,
    ( k2_xboole_0(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) = u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_3'))
    | ~ v1_pre_topc(k1_tsep_1('#skF_1','#skF_4','#skF_3'))
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_4669,c_4792])).

tff(c_4810,plain,
    ( k2_xboole_0(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) = u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_3'))
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_36,c_40,c_4675,c_4796])).

tff(c_4811,plain,(
    k2_xboole_0(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) = u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_38,c_42,c_4672,c_4810])).

tff(c_176,plain,(
    ! [B_90] :
      ( r1_tarski(u1_struct_0(B_90),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_90,'#skF_3')
      | ~ m1_pre_topc(B_90,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_144])).

tff(c_183,plain,(
    ! [B_90] :
      ( k2_xboole_0(u1_struct_0(B_90),u1_struct_0('#skF_3')) = u1_struct_0('#skF_3')
      | ~ m1_pre_topc(B_90,'#skF_3')
      | ~ m1_pre_topc(B_90,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_176,c_2])).

tff(c_5041,plain,
    ( u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_3')) = u1_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4811,c_183])).

tff(c_5065,plain,(
    u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_3')) = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_5041])).

tff(c_4798,plain,
    ( k2_xboole_0(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) = u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_4','#skF_3'),'#skF_1')
    | ~ v1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'))
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4548,c_4792])).

tff(c_4813,plain,
    ( k2_xboole_0(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) = u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_3'))
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_3'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_40,c_36,c_4548,c_4675,c_4548,c_4669,c_4548,c_4798])).

tff(c_4814,plain,(
    k2_xboole_0(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) = u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_42,c_38,c_4672,c_4813])).

tff(c_5071,plain,(
    k2_xboole_0(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5065,c_4814])).

tff(c_5967,plain,(
    ! [A_327] :
      ( r1_tarski(k2_xboole_0(A_327,u1_struct_0('#skF_4')),u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_327,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5071,c_4])).

tff(c_5984,plain,
    ( r1_tarski(u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_2')),u1_struct_0('#skF_3'))
    | ~ r1_tarski(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4821,c_5967])).

tff(c_5998,plain,(
    r1_tarski(u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_2')),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4105,c_5984])).

tff(c_28,plain,(
    ! [B_47,C_49,A_43] :
      ( m1_pre_topc(B_47,C_49)
      | ~ r1_tarski(u1_struct_0(B_47),u1_struct_0(C_49))
      | ~ m1_pre_topc(C_49,A_43)
      | ~ m1_pre_topc(B_47,A_43)
      | ~ l1_pre_topc(A_43)
      | ~ v2_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_6008,plain,(
    ! [A_43] :
      ( m1_pre_topc(k1_tsep_1('#skF_1','#skF_4','#skF_2'),'#skF_3')
      | ~ m1_pre_topc('#skF_3',A_43)
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_4','#skF_2'),A_43)
      | ~ l1_pre_topc(A_43)
      | ~ v2_pre_topc(A_43) ) ),
    inference(resolution,[status(thm)],[c_5998,c_28])).

tff(c_7166,plain,(
    ! [A_344] :
      ( ~ m1_pre_topc('#skF_3',A_344)
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_4','#skF_2'),A_344)
      | ~ l1_pre_topc(A_344)
      | ~ v2_pre_topc(A_344) ) ),
    inference(negUnitSimplification,[status(thm)],[c_4549,c_6008])).

tff(c_7169,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_4570,c_7166])).

tff(c_7181,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_40,c_7169])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:52:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.59/2.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.90/2.60  
% 7.90/2.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.90/2.60  %$ r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k1_tsep_1 > k2_xboole_0 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.90/2.60  
% 7.90/2.60  %Foreground sorts:
% 7.90/2.60  
% 7.90/2.60  
% 7.90/2.60  %Background operators:
% 7.90/2.60  
% 7.90/2.60  
% 7.90/2.60  %Foreground operators:
% 7.90/2.60  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.90/2.60  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 7.90/2.60  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 7.90/2.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.90/2.60  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 7.90/2.60  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.90/2.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.90/2.60  tff('#skF_2', type, '#skF_2': $i).
% 7.90/2.60  tff('#skF_3', type, '#skF_3': $i).
% 7.90/2.60  tff('#skF_1', type, '#skF_1': $i).
% 7.90/2.60  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 7.90/2.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.90/2.60  tff('#skF_4', type, '#skF_4': $i).
% 7.90/2.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.90/2.60  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 7.90/2.60  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.90/2.60  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.90/2.60  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.90/2.60  
% 7.90/2.62  tff(f_197, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => ((m1_pre_topc(B, C) & m1_pre_topc(D, C)) => m1_pre_topc(k1_tsep_1(A, B, D), C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tmap_1)).
% 7.90/2.62  tff(f_64, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => (k1_tsep_1(A, B, C) = k1_tsep_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k1_tsep_1)).
% 7.90/2.62  tff(f_115, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => ((~v2_struct_0(k1_tsep_1(A, B, C)) & v1_pre_topc(k1_tsep_1(A, B, C))) & m1_pre_topc(k1_tsep_1(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 7.90/2.62  tff(f_165, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 7.90/2.62  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 7.90/2.62  tff(f_136, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => m1_pre_topc(B, k1_tsep_1(A, B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_tsep_1)).
% 7.90/2.62  tff(f_40, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 7.90/2.62  tff(f_151, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (k1_tsep_1(A, B, B) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_tmap_1)).
% 7.90/2.62  tff(f_47, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 7.90/2.62  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_xboole_1)).
% 7.90/2.62  tff(f_93, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (((~v2_struct_0(D) & v1_pre_topc(D)) & m1_pre_topc(D, A)) => ((D = k1_tsep_1(A, B, C)) <=> (u1_struct_0(D) = k2_xboole_0(u1_struct_0(B), u1_struct_0(C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tsep_1)).
% 7.90/2.62  tff(c_50, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_197])).
% 7.90/2.62  tff(c_48, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_197])).
% 7.90/2.62  tff(c_40, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_197])).
% 7.90/2.62  tff(c_52, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_197])).
% 7.90/2.62  tff(c_46, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_197])).
% 7.90/2.62  tff(c_38, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_197])).
% 7.90/2.62  tff(c_44, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_197])).
% 7.90/2.62  tff(c_36, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_197])).
% 7.90/2.62  tff(c_4433, plain, (![A_304, C_305, B_306]: (k1_tsep_1(A_304, C_305, B_306)=k1_tsep_1(A_304, B_306, C_305) | ~m1_pre_topc(C_305, A_304) | v2_struct_0(C_305) | ~m1_pre_topc(B_306, A_304) | v2_struct_0(B_306) | ~l1_pre_topc(A_304) | v2_struct_0(A_304))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.90/2.62  tff(c_4445, plain, (![B_306]: (k1_tsep_1('#skF_1', B_306, '#skF_4')=k1_tsep_1('#skF_1', '#skF_4', B_306) | v2_struct_0('#skF_4') | ~m1_pre_topc(B_306, '#skF_1') | v2_struct_0(B_306) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_4433])).
% 7.90/2.62  tff(c_4470, plain, (![B_306]: (k1_tsep_1('#skF_1', B_306, '#skF_4')=k1_tsep_1('#skF_1', '#skF_4', B_306) | v2_struct_0('#skF_4') | ~m1_pre_topc(B_306, '#skF_1') | v2_struct_0(B_306) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_4445])).
% 7.90/2.62  tff(c_4521, plain, (![B_308]: (k1_tsep_1('#skF_1', B_308, '#skF_4')=k1_tsep_1('#skF_1', '#skF_4', B_308) | ~m1_pre_topc(B_308, '#skF_1') | v2_struct_0(B_308))), inference(negUnitSimplification, [status(thm)], [c_52, c_38, c_4470])).
% 7.90/2.62  tff(c_4531, plain, (k1_tsep_1('#skF_1', '#skF_2', '#skF_4')=k1_tsep_1('#skF_1', '#skF_4', '#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_4521])).
% 7.90/2.62  tff(c_4545, plain, (k1_tsep_1('#skF_1', '#skF_2', '#skF_4')=k1_tsep_1('#skF_1', '#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_46, c_4531])).
% 7.90/2.62  tff(c_16, plain, (![A_30, B_31, C_32]: (m1_pre_topc(k1_tsep_1(A_30, B_31, C_32), A_30) | ~m1_pre_topc(C_32, A_30) | v2_struct_0(C_32) | ~m1_pre_topc(B_31, A_30) | v2_struct_0(B_31) | ~l1_pre_topc(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.90/2.62  tff(c_4556, plain, (m1_pre_topc(k1_tsep_1('#skF_1', '#skF_4', '#skF_2'), '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4545, c_16])).
% 7.90/2.62  tff(c_4569, plain, (m1_pre_topc(k1_tsep_1('#skF_1', '#skF_4', '#skF_2'), '#skF_1') | v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_36, c_4556])).
% 7.90/2.62  tff(c_4570, plain, (m1_pre_topc(k1_tsep_1('#skF_1', '#skF_4', '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_52, c_46, c_38, c_4569])).
% 7.90/2.62  tff(c_30, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_197])).
% 7.90/2.62  tff(c_4549, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_4', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4545, c_30])).
% 7.90/2.62  tff(c_34, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_197])).
% 7.90/2.62  tff(c_134, plain, (![B_85, C_86, A_87]: (r1_tarski(u1_struct_0(B_85), u1_struct_0(C_86)) | ~m1_pre_topc(B_85, C_86) | ~m1_pre_topc(C_86, A_87) | ~m1_pre_topc(B_85, A_87) | ~l1_pre_topc(A_87) | ~v2_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_165])).
% 7.90/2.62  tff(c_144, plain, (![B_85]: (r1_tarski(u1_struct_0(B_85), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_85, '#skF_3') | ~m1_pre_topc(B_85, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_40, c_134])).
% 7.90/2.62  tff(c_159, plain, (![B_85]: (r1_tarski(u1_struct_0(B_85), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_85, '#skF_3') | ~m1_pre_topc(B_85, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_144])).
% 7.90/2.62  tff(c_138, plain, (![B_85]: (r1_tarski(u1_struct_0(B_85), u1_struct_0('#skF_2')) | ~m1_pre_topc(B_85, '#skF_2') | ~m1_pre_topc(B_85, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_134])).
% 7.90/2.62  tff(c_168, plain, (![B_89]: (r1_tarski(u1_struct_0(B_89), u1_struct_0('#skF_2')) | ~m1_pre_topc(B_89, '#skF_2') | ~m1_pre_topc(B_89, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_138])).
% 7.90/2.62  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(A_1, B_2)=B_2 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.90/2.62  tff(c_175, plain, (![B_89]: (k2_xboole_0(u1_struct_0(B_89), u1_struct_0('#skF_2'))=u1_struct_0('#skF_2') | ~m1_pre_topc(B_89, '#skF_2') | ~m1_pre_topc(B_89, '#skF_1'))), inference(resolution, [status(thm)], [c_168, c_2])).
% 7.90/2.62  tff(c_2162, plain, (![B_202, A_203, C_204]: (m1_pre_topc(B_202, k1_tsep_1(A_203, B_202, C_204)) | ~m1_pre_topc(C_204, A_203) | v2_struct_0(C_204) | ~m1_pre_topc(B_202, A_203) | v2_struct_0(B_202) | ~l1_pre_topc(A_203) | ~v2_pre_topc(A_203) | v2_struct_0(A_203))), inference(cnfTransformation, [status(thm)], [f_136])).
% 7.90/2.62  tff(c_53, plain, (![B_61, A_62]: (l1_pre_topc(B_61) | ~m1_pre_topc(B_61, A_62) | ~l1_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.90/2.62  tff(c_59, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_53])).
% 7.90/2.62  tff(c_74, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_59])).
% 7.90/2.62  tff(c_2044, plain, (![A_195, B_196]: (k1_tsep_1(A_195, B_196, B_196)=g1_pre_topc(u1_struct_0(B_196), u1_pre_topc(B_196)) | ~m1_pre_topc(B_196, A_195) | v2_struct_0(B_196) | ~l1_pre_topc(A_195) | ~v2_pre_topc(A_195) | v2_struct_0(A_195))), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.90/2.62  tff(c_2052, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k1_tsep_1('#skF_1', '#skF_2', '#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_2044])).
% 7.90/2.62  tff(c_2070, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k1_tsep_1('#skF_1', '#skF_2', '#skF_2') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_2052])).
% 7.90/2.62  tff(c_2071, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k1_tsep_1('#skF_1', '#skF_2', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_52, c_46, c_2070])).
% 7.90/2.62  tff(c_8, plain, (![B_11, A_9]: (m1_pre_topc(B_11, A_9) | ~m1_pre_topc(B_11, g1_pre_topc(u1_struct_0(A_9), u1_pre_topc(A_9))) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.90/2.62  tff(c_2096, plain, (![B_11]: (m1_pre_topc(B_11, '#skF_2') | ~m1_pre_topc(B_11, k1_tsep_1('#skF_1', '#skF_2', '#skF_2')) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2071, c_8])).
% 7.90/2.62  tff(c_2100, plain, (![B_11]: (m1_pre_topc(B_11, '#skF_2') | ~m1_pre_topc(B_11, k1_tsep_1('#skF_1', '#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2096])).
% 7.90/2.62  tff(c_2166, plain, (m1_pre_topc('#skF_2', '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2162, c_2100])).
% 7.90/2.62  tff(c_2184, plain, (m1_pre_topc('#skF_2', '#skF_2') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_44, c_2166])).
% 7.90/2.62  tff(c_2185, plain, (m1_pre_topc('#skF_2', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_52, c_46, c_2184])).
% 7.90/2.62  tff(c_150, plain, (![B_85]: (r1_tarski(u1_struct_0(B_85), u1_struct_0('#skF_2')) | ~m1_pre_topc(B_85, '#skF_2') | ~m1_pre_topc(B_85, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_138])).
% 7.90/2.62  tff(c_185, plain, (![B_91]: (k2_xboole_0(u1_struct_0(B_91), u1_struct_0('#skF_2'))=u1_struct_0('#skF_2') | ~m1_pre_topc(B_91, '#skF_2') | ~m1_pre_topc(B_91, '#skF_1'))), inference(resolution, [status(thm)], [c_168, c_2])).
% 7.90/2.62  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_tarski(k2_xboole_0(A_3, C_5), k2_xboole_0(B_4, C_5)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.90/2.62  tff(c_299, plain, (![B_103, B_104]: (r1_tarski(u1_struct_0('#skF_2'), k2_xboole_0(B_103, u1_struct_0('#skF_2'))) | ~r1_tarski(u1_struct_0(B_104), B_103) | ~m1_pre_topc(B_104, '#skF_2') | ~m1_pre_topc(B_104, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_185, c_4])).
% 7.90/2.62  tff(c_307, plain, (![B_85]: (r1_tarski(u1_struct_0('#skF_2'), k2_xboole_0(u1_struct_0('#skF_2'), u1_struct_0('#skF_2'))) | ~m1_pre_topc(B_85, '#skF_2') | ~m1_pre_topc(B_85, '#skF_1'))), inference(resolution, [status(thm)], [c_150, c_299])).
% 7.90/2.62  tff(c_309, plain, (![B_85]: (~m1_pre_topc(B_85, '#skF_2') | ~m1_pre_topc(B_85, '#skF_1'))), inference(splitLeft, [status(thm)], [c_307])).
% 7.90/2.62  tff(c_2201, plain, (~m1_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_2185, c_309])).
% 7.90/2.62  tff(c_2214, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_2201])).
% 7.90/2.62  tff(c_2215, plain, (r1_tarski(u1_struct_0('#skF_2'), k2_xboole_0(u1_struct_0('#skF_2'), u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_307])).
% 7.90/2.62  tff(c_2229, plain, (r1_tarski(u1_struct_0('#skF_2'), u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_2', '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_175, c_2215])).
% 7.90/2.62  tff(c_2238, plain, (r1_tarski(u1_struct_0('#skF_2'), u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_2229])).
% 7.90/2.62  tff(c_2239, plain, (~m1_pre_topc('#skF_2', '#skF_2')), inference(splitLeft, [status(thm)], [c_2238])).
% 7.90/2.62  tff(c_3403, plain, (![B_266, A_267, C_268]: (m1_pre_topc(B_266, k1_tsep_1(A_267, B_266, C_268)) | ~m1_pre_topc(C_268, A_267) | v2_struct_0(C_268) | ~m1_pre_topc(B_266, A_267) | v2_struct_0(B_266) | ~l1_pre_topc(A_267) | ~v2_pre_topc(A_267) | v2_struct_0(A_267))), inference(cnfTransformation, [status(thm)], [f_136])).
% 7.90/2.62  tff(c_3316, plain, (![A_259, B_260]: (k1_tsep_1(A_259, B_260, B_260)=g1_pre_topc(u1_struct_0(B_260), u1_pre_topc(B_260)) | ~m1_pre_topc(B_260, A_259) | v2_struct_0(B_260) | ~l1_pre_topc(A_259) | ~v2_pre_topc(A_259) | v2_struct_0(A_259))), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.90/2.62  tff(c_3324, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k1_tsep_1('#skF_1', '#skF_2', '#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_3316])).
% 7.90/2.62  tff(c_3342, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k1_tsep_1('#skF_1', '#skF_2', '#skF_2') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_3324])).
% 7.90/2.62  tff(c_3343, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k1_tsep_1('#skF_1', '#skF_2', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_52, c_46, c_3342])).
% 7.90/2.62  tff(c_3368, plain, (![B_11]: (m1_pre_topc(B_11, '#skF_2') | ~m1_pre_topc(B_11, k1_tsep_1('#skF_1', '#skF_2', '#skF_2')) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3343, c_8])).
% 7.90/2.62  tff(c_3372, plain, (![B_11]: (m1_pre_topc(B_11, '#skF_2') | ~m1_pre_topc(B_11, k1_tsep_1('#skF_1', '#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_3368])).
% 7.90/2.62  tff(c_3407, plain, (m1_pre_topc('#skF_2', '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_3403, c_3372])).
% 7.90/2.62  tff(c_3425, plain, (m1_pre_topc('#skF_2', '#skF_2') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_44, c_3407])).
% 7.90/2.62  tff(c_3427, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_46, c_2239, c_3425])).
% 7.90/2.62  tff(c_3429, plain, (m1_pre_topc('#skF_2', '#skF_2')), inference(splitRight, [status(thm)], [c_2238])).
% 7.90/2.62  tff(c_306, plain, (![B_85]: (r1_tarski(u1_struct_0('#skF_2'), k2_xboole_0(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))) | ~m1_pre_topc(B_85, '#skF_2') | ~m1_pre_topc(B_85, '#skF_3') | ~m1_pre_topc(B_85, '#skF_1'))), inference(resolution, [status(thm)], [c_159, c_299])).
% 7.90/2.62  tff(c_3502, plain, (![B_269]: (~m1_pre_topc(B_269, '#skF_2') | ~m1_pre_topc(B_269, '#skF_3') | ~m1_pre_topc(B_269, '#skF_1'))), inference(splitLeft, [status(thm)], [c_306])).
% 7.90/2.62  tff(c_3505, plain, (~m1_pre_topc('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_3429, c_3502])).
% 7.90/2.62  tff(c_3509, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_34, c_3505])).
% 7.90/2.62  tff(c_3510, plain, (r1_tarski(u1_struct_0('#skF_2'), k2_xboole_0(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_306])).
% 7.90/2.62  tff(c_3531, plain, (k2_xboole_0(u1_struct_0('#skF_2'), k2_xboole_0(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))=k2_xboole_0(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_3510, c_2])).
% 7.90/2.62  tff(c_85, plain, (![A_65, C_66, B_67]: (r1_tarski(k2_xboole_0(A_65, C_66), k2_xboole_0(B_67, C_66)) | ~r1_tarski(A_65, B_67))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.90/2.62  tff(c_91, plain, (![A_70, C_71, B_72]: (k2_xboole_0(k2_xboole_0(A_70, C_71), k2_xboole_0(B_72, C_71))=k2_xboole_0(B_72, C_71) | ~r1_tarski(A_70, B_72))), inference(resolution, [status(thm)], [c_85, c_2])).
% 7.90/2.62  tff(c_106, plain, (![A_3, B_72, C_71, A_70]: (r1_tarski(k2_xboole_0(A_3, k2_xboole_0(B_72, C_71)), k2_xboole_0(B_72, C_71)) | ~r1_tarski(A_3, k2_xboole_0(A_70, C_71)) | ~r1_tarski(A_70, B_72))), inference(superposition, [status(thm), theory('equality')], [c_91, c_4])).
% 7.90/2.62  tff(c_3965, plain, (![B_291]: (r1_tarski(k2_xboole_0(u1_struct_0('#skF_2'), k2_xboole_0(B_291, u1_struct_0('#skF_2'))), k2_xboole_0(B_291, u1_struct_0('#skF_2'))) | ~r1_tarski(u1_struct_0('#skF_2'), B_291))), inference(resolution, [status(thm)], [c_2215, c_106])).
% 7.90/2.62  tff(c_3988, plain, (r1_tarski(k2_xboole_0(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')), k2_xboole_0(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))) | ~r1_tarski(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3531, c_3965])).
% 7.90/2.62  tff(c_4096, plain, (~r1_tarski(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_3988])).
% 7.90/2.62  tff(c_4099, plain, (~m1_pre_topc('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_159, c_4096])).
% 7.90/2.62  tff(c_4103, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_34, c_4099])).
% 7.90/2.62  tff(c_4105, plain, (r1_tarski(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_3988])).
% 7.90/2.62  tff(c_20, plain, (![A_30, B_31, C_32]: (~v2_struct_0(k1_tsep_1(A_30, B_31, C_32)) | ~m1_pre_topc(C_32, A_30) | v2_struct_0(C_32) | ~m1_pre_topc(B_31, A_30) | v2_struct_0(B_31) | ~l1_pre_topc(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.90/2.62  tff(c_4559, plain, (~v2_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_2')) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4545, c_20])).
% 7.90/2.62  tff(c_4572, plain, (~v2_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_2')) | v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_36, c_4559])).
% 7.90/2.62  tff(c_4573, plain, (~v2_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_52, c_46, c_38, c_4572])).
% 7.90/2.62  tff(c_18, plain, (![A_30, B_31, C_32]: (v1_pre_topc(k1_tsep_1(A_30, B_31, C_32)) | ~m1_pre_topc(C_32, A_30) | v2_struct_0(C_32) | ~m1_pre_topc(B_31, A_30) | v2_struct_0(B_31) | ~l1_pre_topc(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.90/2.62  tff(c_4562, plain, (v1_pre_topc(k1_tsep_1('#skF_1', '#skF_4', '#skF_2')) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4545, c_18])).
% 7.90/2.62  tff(c_4575, plain, (v1_pre_topc(k1_tsep_1('#skF_1', '#skF_4', '#skF_2')) | v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_36, c_4562])).
% 7.90/2.62  tff(c_4576, plain, (v1_pre_topc(k1_tsep_1('#skF_1', '#skF_4', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_52, c_46, c_38, c_4575])).
% 7.90/2.62  tff(c_4792, plain, (![A_314, B_315, C_316]: (u1_struct_0(k1_tsep_1(A_314, B_315, C_316))=k2_xboole_0(u1_struct_0(B_315), u1_struct_0(C_316)) | ~m1_pre_topc(k1_tsep_1(A_314, B_315, C_316), A_314) | ~v1_pre_topc(k1_tsep_1(A_314, B_315, C_316)) | v2_struct_0(k1_tsep_1(A_314, B_315, C_316)) | ~m1_pre_topc(C_316, A_314) | v2_struct_0(C_316) | ~m1_pre_topc(B_315, A_314) | v2_struct_0(B_315) | ~l1_pre_topc(A_314) | v2_struct_0(A_314))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.90/2.62  tff(c_4802, plain, (k2_xboole_0(u1_struct_0('#skF_2'), u1_struct_0('#skF_4'))=u1_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_4')) | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_4', '#skF_2'), '#skF_1') | ~v1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_4')) | v2_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4545, c_4792])).
% 7.90/2.62  tff(c_4820, plain, (k2_xboole_0(u1_struct_0('#skF_2'), u1_struct_0('#skF_4'))=u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_2')) | v2_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_2')) | v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_36, c_4545, c_4576, c_4545, c_4570, c_4545, c_4802])).
% 7.90/2.62  tff(c_4821, plain, (k2_xboole_0(u1_struct_0('#skF_2'), u1_struct_0('#skF_4'))=u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_52, c_46, c_38, c_4573, c_4820])).
% 7.90/2.62  tff(c_32, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_197])).
% 7.90/2.62  tff(c_42, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_197])).
% 7.90/2.62  tff(c_4534, plain, (k1_tsep_1('#skF_1', '#skF_3', '#skF_4')=k1_tsep_1('#skF_1', '#skF_4', '#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_40, c_4521])).
% 7.90/2.62  tff(c_4548, plain, (k1_tsep_1('#skF_1', '#skF_3', '#skF_4')=k1_tsep_1('#skF_1', '#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_42, c_4534])).
% 7.90/2.62  tff(c_4658, plain, (~v2_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_3')) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4548, c_20])).
% 7.90/2.62  tff(c_4671, plain, (~v2_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_3')) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_40, c_36, c_4658])).
% 7.90/2.62  tff(c_4672, plain, (~v2_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_52, c_42, c_38, c_4671])).
% 7.90/2.62  tff(c_4661, plain, (v1_pre_topc(k1_tsep_1('#skF_1', '#skF_4', '#skF_3')) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4548, c_18])).
% 7.90/2.63  tff(c_4674, plain, (v1_pre_topc(k1_tsep_1('#skF_1', '#skF_4', '#skF_3')) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_40, c_36, c_4661])).
% 7.90/2.63  tff(c_4675, plain, (v1_pre_topc(k1_tsep_1('#skF_1', '#skF_4', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_52, c_42, c_38, c_4674])).
% 7.90/2.63  tff(c_4655, plain, (m1_pre_topc(k1_tsep_1('#skF_1', '#skF_4', '#skF_3'), '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4548, c_16])).
% 7.90/2.63  tff(c_4668, plain, (m1_pre_topc(k1_tsep_1('#skF_1', '#skF_4', '#skF_3'), '#skF_1') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_40, c_36, c_4655])).
% 7.90/2.63  tff(c_4669, plain, (m1_pre_topc(k1_tsep_1('#skF_1', '#skF_4', '#skF_3'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_52, c_42, c_38, c_4668])).
% 7.90/2.63  tff(c_4796, plain, (k2_xboole_0(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))=u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_3')) | ~v1_pre_topc(k1_tsep_1('#skF_1', '#skF_4', '#skF_3')) | v2_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_4669, c_4792])).
% 7.90/2.63  tff(c_4810, plain, (k2_xboole_0(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))=u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_3')) | v2_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_3')) | v2_struct_0('#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_36, c_40, c_4675, c_4796])).
% 7.90/2.63  tff(c_4811, plain, (k2_xboole_0(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))=u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_52, c_38, c_42, c_4672, c_4810])).
% 7.90/2.63  tff(c_176, plain, (![B_90]: (r1_tarski(u1_struct_0(B_90), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_90, '#skF_3') | ~m1_pre_topc(B_90, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_144])).
% 7.90/2.63  tff(c_183, plain, (![B_90]: (k2_xboole_0(u1_struct_0(B_90), u1_struct_0('#skF_3'))=u1_struct_0('#skF_3') | ~m1_pre_topc(B_90, '#skF_3') | ~m1_pre_topc(B_90, '#skF_1'))), inference(resolution, [status(thm)], [c_176, c_2])).
% 7.90/2.63  tff(c_5041, plain, (u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_3'))=u1_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4811, c_183])).
% 7.90/2.63  tff(c_5065, plain, (u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_3'))=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_5041])).
% 7.90/2.63  tff(c_4798, plain, (k2_xboole_0(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))=u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_4', '#skF_3'), '#skF_1') | ~v1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')) | v2_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4548, c_4792])).
% 7.90/2.63  tff(c_4813, plain, (k2_xboole_0(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))=u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_3')) | v2_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_3')) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_40, c_36, c_4548, c_4675, c_4548, c_4669, c_4548, c_4798])).
% 7.90/2.63  tff(c_4814, plain, (k2_xboole_0(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))=u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_52, c_42, c_38, c_4672, c_4813])).
% 7.90/2.63  tff(c_5071, plain, (k2_xboole_0(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5065, c_4814])).
% 7.90/2.63  tff(c_5967, plain, (![A_327]: (r1_tarski(k2_xboole_0(A_327, u1_struct_0('#skF_4')), u1_struct_0('#skF_3')) | ~r1_tarski(A_327, u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_5071, c_4])).
% 7.90/2.63  tff(c_5984, plain, (r1_tarski(u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_2')), u1_struct_0('#skF_3')) | ~r1_tarski(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_4821, c_5967])).
% 7.90/2.63  tff(c_5998, plain, (r1_tarski(u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_2')), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4105, c_5984])).
% 7.90/2.63  tff(c_28, plain, (![B_47, C_49, A_43]: (m1_pre_topc(B_47, C_49) | ~r1_tarski(u1_struct_0(B_47), u1_struct_0(C_49)) | ~m1_pre_topc(C_49, A_43) | ~m1_pre_topc(B_47, A_43) | ~l1_pre_topc(A_43) | ~v2_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_165])).
% 7.90/2.63  tff(c_6008, plain, (![A_43]: (m1_pre_topc(k1_tsep_1('#skF_1', '#skF_4', '#skF_2'), '#skF_3') | ~m1_pre_topc('#skF_3', A_43) | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_4', '#skF_2'), A_43) | ~l1_pre_topc(A_43) | ~v2_pre_topc(A_43))), inference(resolution, [status(thm)], [c_5998, c_28])).
% 7.90/2.63  tff(c_7166, plain, (![A_344]: (~m1_pre_topc('#skF_3', A_344) | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_4', '#skF_2'), A_344) | ~l1_pre_topc(A_344) | ~v2_pre_topc(A_344))), inference(negUnitSimplification, [status(thm)], [c_4549, c_6008])).
% 7.90/2.63  tff(c_7169, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_4570, c_7166])).
% 7.90/2.63  tff(c_7181, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_40, c_7169])).
% 7.90/2.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.90/2.63  
% 7.90/2.63  Inference rules
% 7.90/2.63  ----------------------
% 7.90/2.63  #Ref     : 0
% 7.90/2.63  #Sup     : 1702
% 7.90/2.63  #Fact    : 0
% 7.90/2.63  #Define  : 0
% 7.90/2.63  #Split   : 30
% 7.90/2.63  #Chain   : 0
% 7.90/2.63  #Close   : 0
% 7.90/2.63  
% 7.90/2.63  Ordering : KBO
% 7.90/2.63  
% 7.90/2.63  Simplification rules
% 7.90/2.63  ----------------------
% 7.90/2.63  #Subsume      : 221
% 7.90/2.63  #Demod        : 1292
% 7.90/2.63  #Tautology    : 435
% 7.90/2.63  #SimpNegUnit  : 327
% 7.90/2.63  #BackRed      : 16
% 7.90/2.63  
% 7.90/2.63  #Partial instantiations: 0
% 7.90/2.63  #Strategies tried      : 1
% 7.90/2.63  
% 7.90/2.63  Timing (in seconds)
% 7.90/2.63  ----------------------
% 7.90/2.63  Preprocessing        : 0.34
% 7.90/2.63  Parsing              : 0.19
% 7.90/2.63  CNF conversion       : 0.03
% 7.90/2.63  Main loop            : 1.50
% 7.90/2.63  Inferencing          : 0.48
% 7.90/2.63  Reduction            : 0.50
% 7.90/2.63  Demodulation         : 0.35
% 7.90/2.63  BG Simplification    : 0.06
% 7.90/2.63  Subsumption          : 0.35
% 7.90/2.63  Abstraction          : 0.07
% 7.90/2.63  MUC search           : 0.00
% 7.90/2.63  Cooper               : 0.00
% 7.90/2.63  Total                : 1.90
% 7.90/2.63  Index Insertion      : 0.00
% 7.90/2.63  Index Deletion       : 0.00
% 7.90/2.63  Index Matching       : 0.00
% 7.90/2.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
