%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1930+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:41 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :   57 (  71 expanded)
%              Number of leaves         :   31 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :  166 ( 266 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_waybel_0 > r1_waybel_0 > r1_orders_2 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k2_waybel_0 > #nlpp > u1_struct_0 > #skF_7 > #skF_10 > #skF_5 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3 > #skF_1 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff(r2_waybel_0,type,(
    r2_waybel_0: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k2_waybel_0,type,(
    k2_waybel_0: ( $i * $i * $i ) > $i )).

tff(v7_waybel_0,type,(
    v7_waybel_0: $i > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(r1_waybel_0,type,(
    r1_waybel_0: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_120,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v4_orders_2(B)
              & v7_waybel_0(B)
              & l1_waybel_0(B,A) )
           => ! [C] :
                ( r1_waybel_0(A,B,C)
               => r2_waybel_0(A,B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_yellow_6)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => l1_orders_2(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_0)).

tff(f_72,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( r2_waybel_0(A,B,C)
            <=> ! [D] :
                  ( m1_subset_1(D,u1_struct_0(B))
                 => ? [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                      & r1_orders_2(B,D,E)
                      & r2_hidden(k2_waybel_0(A,B,E),C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_waybel_0)).

tff(f_48,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( r1_waybel_0(A,B,C)
            <=> ? [D] :
                  ( m1_subset_1(D,u1_struct_0(B))
                  & ! [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                     => ( r1_orders_2(B,D,E)
                       => r2_hidden(k2_waybel_0(A,B,E),C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_waybel_0)).

tff(f_92,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ( v7_waybel_0(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ? [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                    & r1_orders_2(A,B,D)
                    & r1_orders_2(A,C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_yellow_6)).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_48,plain,(
    l1_struct_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_40,plain,(
    l1_waybel_0('#skF_9','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_38,plain,(
    r1_waybel_0('#skF_8','#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_51,plain,(
    ! [B_140,A_141] :
      ( l1_orders_2(B_140)
      | ~ l1_waybel_0(B_140,A_141)
      | ~ l1_struct_0(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_54,plain,
    ( l1_orders_2('#skF_9')
    | ~ l1_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_40,c_51])).

tff(c_57,plain,(
    l1_orders_2('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_54])).

tff(c_42,plain,(
    v7_waybel_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_20,plain,(
    ! [A_54,B_82,C_96] :
      ( m1_subset_1('#skF_3'(A_54,B_82,C_96),u1_struct_0(B_82))
      | r2_waybel_0(A_54,B_82,C_96)
      | ~ l1_waybel_0(B_82,A_54)
      | v2_struct_0(B_82)
      | ~ l1_struct_0(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_4,plain,(
    ! [A_1,B_29,C_43] :
      ( m1_subset_1('#skF_2'(A_1,B_29,C_43),u1_struct_0(B_29))
      | ~ r1_waybel_0(A_1,B_29,C_43)
      | ~ l1_waybel_0(B_29,A_1)
      | v2_struct_0(B_29)
      | ~ l1_struct_0(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_32,plain,(
    ! [A_107,B_122,C_126] :
      ( m1_subset_1('#skF_5'(A_107,B_122,C_126),u1_struct_0(A_107))
      | ~ m1_subset_1(C_126,u1_struct_0(A_107))
      | ~ m1_subset_1(B_122,u1_struct_0(A_107))
      | ~ v7_waybel_0(A_107)
      | ~ l1_orders_2(A_107)
      | v2_struct_0(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_30,plain,(
    ! [A_107,B_122,C_126] :
      ( r1_orders_2(A_107,B_122,'#skF_5'(A_107,B_122,C_126))
      | ~ m1_subset_1(C_126,u1_struct_0(A_107))
      | ~ m1_subset_1(B_122,u1_struct_0(A_107))
      | ~ v7_waybel_0(A_107)
      | ~ l1_orders_2(A_107)
      | v2_struct_0(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_92,plain,(
    ! [A_185,B_186,E_187,C_188] :
      ( r2_hidden(k2_waybel_0(A_185,B_186,E_187),C_188)
      | ~ r1_orders_2(B_186,'#skF_2'(A_185,B_186,C_188),E_187)
      | ~ m1_subset_1(E_187,u1_struct_0(B_186))
      | ~ r1_waybel_0(A_185,B_186,C_188)
      | ~ l1_waybel_0(B_186,A_185)
      | v2_struct_0(B_186)
      | ~ l1_struct_0(A_185)
      | v2_struct_0(A_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_111,plain,(
    ! [A_185,A_107,C_188,C_126] :
      ( r2_hidden(k2_waybel_0(A_185,A_107,'#skF_5'(A_107,'#skF_2'(A_185,A_107,C_188),C_126)),C_188)
      | ~ m1_subset_1('#skF_5'(A_107,'#skF_2'(A_185,A_107,C_188),C_126),u1_struct_0(A_107))
      | ~ r1_waybel_0(A_185,A_107,C_188)
      | ~ l1_waybel_0(A_107,A_185)
      | ~ l1_struct_0(A_185)
      | v2_struct_0(A_185)
      | ~ m1_subset_1(C_126,u1_struct_0(A_107))
      | ~ m1_subset_1('#skF_2'(A_185,A_107,C_188),u1_struct_0(A_107))
      | ~ v7_waybel_0(A_107)
      | ~ l1_orders_2(A_107)
      | v2_struct_0(A_107) ) ),
    inference(resolution,[status(thm)],[c_30,c_92])).

tff(c_28,plain,(
    ! [A_107,C_126,B_122] :
      ( r1_orders_2(A_107,C_126,'#skF_5'(A_107,B_122,C_126))
      | ~ m1_subset_1(C_126,u1_struct_0(A_107))
      | ~ m1_subset_1(B_122,u1_struct_0(A_107))
      | ~ v7_waybel_0(A_107)
      | ~ l1_orders_2(A_107)
      | v2_struct_0(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_113,plain,(
    ! [A_189,B_190,E_191,C_192] :
      ( ~ r2_hidden(k2_waybel_0(A_189,B_190,E_191),C_192)
      | ~ r1_orders_2(B_190,'#skF_3'(A_189,B_190,C_192),E_191)
      | ~ m1_subset_1(E_191,u1_struct_0(B_190))
      | r2_waybel_0(A_189,B_190,C_192)
      | ~ l1_waybel_0(B_190,A_189)
      | v2_struct_0(B_190)
      | ~ l1_struct_0(A_189)
      | v2_struct_0(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_138,plain,(
    ! [A_207,A_208,B_209,C_210] :
      ( ~ r2_hidden(k2_waybel_0(A_207,A_208,'#skF_5'(A_208,B_209,'#skF_3'(A_207,A_208,C_210))),C_210)
      | ~ m1_subset_1('#skF_5'(A_208,B_209,'#skF_3'(A_207,A_208,C_210)),u1_struct_0(A_208))
      | r2_waybel_0(A_207,A_208,C_210)
      | ~ l1_waybel_0(A_208,A_207)
      | ~ l1_struct_0(A_207)
      | v2_struct_0(A_207)
      | ~ m1_subset_1('#skF_3'(A_207,A_208,C_210),u1_struct_0(A_208))
      | ~ m1_subset_1(B_209,u1_struct_0(A_208))
      | ~ v7_waybel_0(A_208)
      | ~ l1_orders_2(A_208)
      | v2_struct_0(A_208) ) ),
    inference(resolution,[status(thm)],[c_28,c_113])).

tff(c_144,plain,(
    ! [A_211,A_212,C_213] :
      ( r2_waybel_0(A_211,A_212,C_213)
      | ~ m1_subset_1('#skF_5'(A_212,'#skF_2'(A_211,A_212,C_213),'#skF_3'(A_211,A_212,C_213)),u1_struct_0(A_212))
      | ~ r1_waybel_0(A_211,A_212,C_213)
      | ~ l1_waybel_0(A_212,A_211)
      | ~ l1_struct_0(A_211)
      | v2_struct_0(A_211)
      | ~ m1_subset_1('#skF_3'(A_211,A_212,C_213),u1_struct_0(A_212))
      | ~ m1_subset_1('#skF_2'(A_211,A_212,C_213),u1_struct_0(A_212))
      | ~ v7_waybel_0(A_212)
      | ~ l1_orders_2(A_212)
      | v2_struct_0(A_212) ) ),
    inference(resolution,[status(thm)],[c_111,c_138])).

tff(c_150,plain,(
    ! [A_214,A_215,C_216] :
      ( r2_waybel_0(A_214,A_215,C_216)
      | ~ r1_waybel_0(A_214,A_215,C_216)
      | ~ l1_waybel_0(A_215,A_214)
      | ~ l1_struct_0(A_214)
      | v2_struct_0(A_214)
      | ~ m1_subset_1('#skF_3'(A_214,A_215,C_216),u1_struct_0(A_215))
      | ~ m1_subset_1('#skF_2'(A_214,A_215,C_216),u1_struct_0(A_215))
      | ~ v7_waybel_0(A_215)
      | ~ l1_orders_2(A_215)
      | v2_struct_0(A_215) ) ),
    inference(resolution,[status(thm)],[c_32,c_144])).

tff(c_155,plain,(
    ! [A_217,B_218,C_219] :
      ( r2_waybel_0(A_217,B_218,C_219)
      | ~ m1_subset_1('#skF_3'(A_217,B_218,C_219),u1_struct_0(B_218))
      | ~ v7_waybel_0(B_218)
      | ~ l1_orders_2(B_218)
      | ~ r1_waybel_0(A_217,B_218,C_219)
      | ~ l1_waybel_0(B_218,A_217)
      | v2_struct_0(B_218)
      | ~ l1_struct_0(A_217)
      | v2_struct_0(A_217) ) ),
    inference(resolution,[status(thm)],[c_4,c_150])).

tff(c_160,plain,(
    ! [B_220,A_221,C_222] :
      ( ~ v7_waybel_0(B_220)
      | ~ l1_orders_2(B_220)
      | ~ r1_waybel_0(A_221,B_220,C_222)
      | r2_waybel_0(A_221,B_220,C_222)
      | ~ l1_waybel_0(B_220,A_221)
      | v2_struct_0(B_220)
      | ~ l1_struct_0(A_221)
      | v2_struct_0(A_221) ) ),
    inference(resolution,[status(thm)],[c_20,c_155])).

tff(c_36,plain,(
    ~ r2_waybel_0('#skF_8','#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_163,plain,
    ( ~ v7_waybel_0('#skF_9')
    | ~ l1_orders_2('#skF_9')
    | ~ r1_waybel_0('#skF_8','#skF_9','#skF_10')
    | ~ l1_waybel_0('#skF_9','#skF_8')
    | v2_struct_0('#skF_9')
    | ~ l1_struct_0('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_160,c_36])).

tff(c_166,plain,
    ( v2_struct_0('#skF_9')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_40,c_38,c_57,c_42,c_163])).

tff(c_168,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_46,c_166])).

%------------------------------------------------------------------------------
