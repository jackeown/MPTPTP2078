%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1583+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:06 EST 2020

% Result     : Theorem 12.94s
% Output     : CNFRefutation 13.29s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 580 expanded)
%              Number of leaves         :   31 ( 216 expanded)
%              Depth                    :   19
%              Number of atoms          :  814 (3344 expanded)
%              Number of equality atoms :    4 ( 127 expanded)
%              Maximal formula depth    :   23 (   8 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > r1_lattice3 > v4_yellow_0 > r2_hidden > m1_yellow_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > #nlpp > u1_struct_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(v4_yellow_0,type,(
    v4_yellow_0: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

tff(m1_yellow_0,type,(
    m1_yellow_0: ( $i * $i ) > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_156,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v4_yellow_0(B,A)
              & m1_yellow_0(B,A) )
           => ! [C,D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ! [E] :
                    ( m1_subset_1(E,u1_struct_0(B))
                   => ( E = D
                     => ( ( r1_lattice3(A,C,D)
                         => r1_lattice3(B,C,E) )
                        & ( r2_lattice3(A,C,D)
                         => r2_lattice3(B,C,E) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_yellow_0)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_yellow_0(B,A)
         => l1_orders_2(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_yellow_0)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r2_lattice3(A,B,C)
          <=> ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_hidden(D,B)
                 => r1_orders_2(A,D,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r1_lattice3(A,B,C)
          <=> ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_hidden(D,B)
                 => r1_orders_2(A,C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattice3)).

tff(f_97,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_yellow_0(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => m1_subset_1(C,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_yellow_0)).

tff(f_81,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_126,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( ( v4_yellow_0(B,A)
            & m1_yellow_0(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ! [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(B))
                         => ( ( E = C
                              & F = D
                              & r1_orders_2(A,C,D)
                              & r2_hidden(E,u1_struct_0(B)) )
                           => r1_orders_2(B,E,F) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_yellow_0)).

tff(f_71,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_32,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_48,plain,
    ( ~ r1_lattice3('#skF_4','#skF_5','#skF_7')
    | ~ r2_lattice3('#skF_4','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_56,plain,
    ( ~ r1_lattice3('#skF_4','#skF_5','#skF_6')
    | ~ r2_lattice3('#skF_4','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_32,c_48])).

tff(c_75,plain,(
    ~ r2_lattice3('#skF_4','#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_34,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_58,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34])).

tff(c_36,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_54,plain,
    ( r1_lattice3('#skF_3','#skF_5','#skF_6')
    | r2_lattice3('#skF_3','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_64,plain,(
    r2_lattice3('#skF_3','#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_44,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_38,plain,(
    m1_yellow_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_67,plain,(
    ! [B_122,A_123] :
      ( l1_orders_2(B_122)
      | ~ m1_yellow_0(B_122,A_123)
      | ~ l1_orders_2(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_70,plain,
    ( l1_orders_2('#skF_4')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_67])).

tff(c_73,plain,(
    l1_orders_2('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_70])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_16,plain,(
    ! [A_13,B_20,C_21] :
      ( m1_subset_1('#skF_2'(A_13,B_20,C_21),u1_struct_0(A_13))
      | r2_lattice3(A_13,B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0(A_13))
      | ~ l1_orders_2(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_18,plain,(
    ! [A_25] :
      ( l1_struct_0(A_25)
      | ~ l1_orders_2(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_40,plain,(
    v4_yellow_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_129,plain,(
    ! [A_151,B_152,C_153] :
      ( m1_subset_1('#skF_1'(A_151,B_152,C_153),u1_struct_0(A_151))
      | r1_lattice3(A_151,B_152,C_153)
      | ~ m1_subset_1(C_153,u1_struct_0(A_151))
      | ~ l1_orders_2(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_28,plain,(
    ! [C_40,A_34,B_38] :
      ( m1_subset_1(C_40,u1_struct_0(A_34))
      | ~ m1_subset_1(C_40,u1_struct_0(B_38))
      | ~ m1_yellow_0(B_38,A_34)
      | v2_struct_0(B_38)
      | ~ l1_orders_2(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_132,plain,(
    ! [A_151,B_152,C_153,A_34] :
      ( m1_subset_1('#skF_1'(A_151,B_152,C_153),u1_struct_0(A_34))
      | ~ m1_yellow_0(A_151,A_34)
      | v2_struct_0(A_151)
      | ~ l1_orders_2(A_34)
      | v2_struct_0(A_34)
      | r1_lattice3(A_151,B_152,C_153)
      | ~ m1_subset_1(C_153,u1_struct_0(A_151))
      | ~ l1_orders_2(A_151) ) ),
    inference(resolution,[status(thm)],[c_129,c_28])).

tff(c_8,plain,(
    ! [A_1,B_8,C_9] :
      ( m1_subset_1('#skF_1'(A_1,B_8,C_9),u1_struct_0(A_1))
      | r1_lattice3(A_1,B_8,C_9)
      | ~ m1_subset_1(C_9,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6,plain,(
    ! [A_1,B_8,C_9] :
      ( r2_hidden('#skF_1'(A_1,B_8,C_9),B_8)
      | r1_lattice3(A_1,B_8,C_9)
      | ~ m1_subset_1(C_9,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_154,plain,(
    ! [A_163,C_164,D_165,B_166] :
      ( r1_orders_2(A_163,C_164,D_165)
      | ~ r2_hidden(D_165,B_166)
      | ~ m1_subset_1(D_165,u1_struct_0(A_163))
      | ~ r1_lattice3(A_163,B_166,C_164)
      | ~ m1_subset_1(C_164,u1_struct_0(A_163))
      | ~ l1_orders_2(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_406,plain,(
    ! [A_260,C_259,A_261,B_258,C_262] :
      ( r1_orders_2(A_260,C_262,'#skF_1'(A_261,B_258,C_259))
      | ~ m1_subset_1('#skF_1'(A_261,B_258,C_259),u1_struct_0(A_260))
      | ~ r1_lattice3(A_260,B_258,C_262)
      | ~ m1_subset_1(C_262,u1_struct_0(A_260))
      | ~ l1_orders_2(A_260)
      | r1_lattice3(A_261,B_258,C_259)
      | ~ m1_subset_1(C_259,u1_struct_0(A_261))
      | ~ l1_orders_2(A_261) ) ),
    inference(resolution,[status(thm)],[c_6,c_154])).

tff(c_667,plain,(
    ! [C_353,B_352,A_351,A_354,C_355] :
      ( r1_orders_2(A_351,C_353,'#skF_1'(A_354,B_352,C_355))
      | ~ r1_lattice3(A_351,B_352,C_353)
      | ~ m1_subset_1(C_353,u1_struct_0(A_351))
      | ~ m1_yellow_0(A_354,A_351)
      | v2_struct_0(A_354)
      | ~ l1_orders_2(A_351)
      | v2_struct_0(A_351)
      | r1_lattice3(A_354,B_352,C_355)
      | ~ m1_subset_1(C_355,u1_struct_0(A_354))
      | ~ l1_orders_2(A_354) ) ),
    inference(resolution,[status(thm)],[c_132,c_406])).

tff(c_26,plain,(
    ! [A_32,B_33] :
      ( r2_hidden(A_32,B_33)
      | v1_xboole_0(B_33)
      | ~ m1_subset_1(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_164,plain,(
    ! [B_167,E_168,F_169,A_170] :
      ( r1_orders_2(B_167,E_168,F_169)
      | ~ r2_hidden(E_168,u1_struct_0(B_167))
      | ~ r1_orders_2(A_170,E_168,F_169)
      | ~ m1_subset_1(F_169,u1_struct_0(B_167))
      | ~ m1_subset_1(E_168,u1_struct_0(B_167))
      | ~ m1_subset_1(F_169,u1_struct_0(A_170))
      | ~ m1_subset_1(E_168,u1_struct_0(A_170))
      | ~ m1_yellow_0(B_167,A_170)
      | ~ v4_yellow_0(B_167,A_170)
      | ~ l1_orders_2(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_176,plain,(
    ! [B_167,A_32,F_169,A_170] :
      ( r1_orders_2(B_167,A_32,F_169)
      | ~ r1_orders_2(A_170,A_32,F_169)
      | ~ m1_subset_1(F_169,u1_struct_0(B_167))
      | ~ m1_subset_1(F_169,u1_struct_0(A_170))
      | ~ m1_subset_1(A_32,u1_struct_0(A_170))
      | ~ m1_yellow_0(B_167,A_170)
      | ~ v4_yellow_0(B_167,A_170)
      | ~ l1_orders_2(A_170)
      | v1_xboole_0(u1_struct_0(B_167))
      | ~ m1_subset_1(A_32,u1_struct_0(B_167)) ) ),
    inference(resolution,[status(thm)],[c_26,c_164])).

tff(c_3137,plain,(
    ! [B_1041,C_1039,C_1037,A_1038,B_1036,A_1040] :
      ( r1_orders_2(B_1036,C_1037,'#skF_1'(A_1038,B_1041,C_1039))
      | ~ m1_subset_1('#skF_1'(A_1038,B_1041,C_1039),u1_struct_0(B_1036))
      | ~ m1_subset_1('#skF_1'(A_1038,B_1041,C_1039),u1_struct_0(A_1040))
      | ~ m1_yellow_0(B_1036,A_1040)
      | ~ v4_yellow_0(B_1036,A_1040)
      | v1_xboole_0(u1_struct_0(B_1036))
      | ~ m1_subset_1(C_1037,u1_struct_0(B_1036))
      | ~ r1_lattice3(A_1040,B_1041,C_1037)
      | ~ m1_subset_1(C_1037,u1_struct_0(A_1040))
      | ~ m1_yellow_0(A_1038,A_1040)
      | v2_struct_0(A_1038)
      | ~ l1_orders_2(A_1040)
      | v2_struct_0(A_1040)
      | r1_lattice3(A_1038,B_1041,C_1039)
      | ~ m1_subset_1(C_1039,u1_struct_0(A_1038))
      | ~ l1_orders_2(A_1038) ) ),
    inference(resolution,[status(thm)],[c_667,c_176])).

tff(c_3516,plain,(
    ! [C_1069,A_1072,B_1068,C_1070,A_1071] :
      ( r1_orders_2(A_1072,C_1069,'#skF_1'(A_1072,B_1068,C_1070))
      | ~ m1_subset_1('#skF_1'(A_1072,B_1068,C_1070),u1_struct_0(A_1071))
      | ~ v4_yellow_0(A_1072,A_1071)
      | v1_xboole_0(u1_struct_0(A_1072))
      | ~ m1_subset_1(C_1069,u1_struct_0(A_1072))
      | ~ r1_lattice3(A_1071,B_1068,C_1069)
      | ~ m1_subset_1(C_1069,u1_struct_0(A_1071))
      | ~ m1_yellow_0(A_1072,A_1071)
      | v2_struct_0(A_1072)
      | ~ l1_orders_2(A_1071)
      | v2_struct_0(A_1071)
      | r1_lattice3(A_1072,B_1068,C_1070)
      | ~ m1_subset_1(C_1070,u1_struct_0(A_1072))
      | ~ l1_orders_2(A_1072) ) ),
    inference(resolution,[status(thm)],[c_8,c_3137])).

tff(c_3594,plain,(
    ! [C_1090,C_1091,B_1088,A_1087,A_1089] :
      ( r1_orders_2(A_1089,C_1091,'#skF_1'(A_1089,B_1088,C_1090))
      | ~ v4_yellow_0(A_1089,A_1087)
      | v1_xboole_0(u1_struct_0(A_1089))
      | ~ m1_subset_1(C_1091,u1_struct_0(A_1089))
      | ~ r1_lattice3(A_1087,B_1088,C_1091)
      | ~ m1_subset_1(C_1091,u1_struct_0(A_1087))
      | ~ m1_yellow_0(A_1089,A_1087)
      | v2_struct_0(A_1089)
      | ~ l1_orders_2(A_1087)
      | v2_struct_0(A_1087)
      | r1_lattice3(A_1089,B_1088,C_1090)
      | ~ m1_subset_1(C_1090,u1_struct_0(A_1089))
      | ~ l1_orders_2(A_1089) ) ),
    inference(resolution,[status(thm)],[c_132,c_3516])).

tff(c_3596,plain,(
    ! [C_1091,B_1088,C_1090] :
      ( r1_orders_2('#skF_4',C_1091,'#skF_1'('#skF_4',B_1088,C_1090))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_1091,u1_struct_0('#skF_4'))
      | ~ r1_lattice3('#skF_3',B_1088,C_1091)
      | ~ m1_subset_1(C_1091,u1_struct_0('#skF_3'))
      | ~ m1_yellow_0('#skF_4','#skF_3')
      | v2_struct_0('#skF_4')
      | ~ l1_orders_2('#skF_3')
      | v2_struct_0('#skF_3')
      | r1_lattice3('#skF_4',B_1088,C_1090)
      | ~ m1_subset_1(C_1090,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40,c_3594])).

tff(c_3599,plain,(
    ! [C_1091,B_1088,C_1090] :
      ( r1_orders_2('#skF_4',C_1091,'#skF_1'('#skF_4',B_1088,C_1090))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_1091,u1_struct_0('#skF_4'))
      | ~ r1_lattice3('#skF_3',B_1088,C_1091)
      | ~ m1_subset_1(C_1091,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | r1_lattice3('#skF_4',B_1088,C_1090)
      | ~ m1_subset_1(C_1090,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_44,c_38,c_3596])).

tff(c_3600,plain,(
    ! [C_1091,B_1088,C_1090] :
      ( r1_orders_2('#skF_4',C_1091,'#skF_1'('#skF_4',B_1088,C_1090))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_1091,u1_struct_0('#skF_4'))
      | ~ r1_lattice3('#skF_3',B_1088,C_1091)
      | ~ m1_subset_1(C_1091,u1_struct_0('#skF_3'))
      | r1_lattice3('#skF_4',B_1088,C_1090)
      | ~ m1_subset_1(C_1090,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_42,c_3599])).

tff(c_3601,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_3600])).

tff(c_22,plain,(
    ! [A_29] :
      ( ~ v1_xboole_0(u1_struct_0(A_29))
      | ~ l1_struct_0(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_3604,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_3601,c_22])).

tff(c_3607,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_3604])).

tff(c_3640,plain,(
    ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_3607])).

tff(c_3644,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_3640])).

tff(c_3646,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_3600])).

tff(c_133,plain,(
    ! [A_154,B_155,C_156] :
      ( m1_subset_1('#skF_2'(A_154,B_155,C_156),u1_struct_0(A_154))
      | r2_lattice3(A_154,B_155,C_156)
      | ~ m1_subset_1(C_156,u1_struct_0(A_154))
      | ~ l1_orders_2(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_136,plain,(
    ! [A_154,B_155,C_156,A_34] :
      ( m1_subset_1('#skF_2'(A_154,B_155,C_156),u1_struct_0(A_34))
      | ~ m1_yellow_0(A_154,A_34)
      | v2_struct_0(A_154)
      | ~ l1_orders_2(A_34)
      | v2_struct_0(A_34)
      | r2_lattice3(A_154,B_155,C_156)
      | ~ m1_subset_1(C_156,u1_struct_0(A_154))
      | ~ l1_orders_2(A_154) ) ),
    inference(resolution,[status(thm)],[c_133,c_28])).

tff(c_14,plain,(
    ! [A_13,B_20,C_21] :
      ( r2_hidden('#skF_2'(A_13,B_20,C_21),B_20)
      | r2_lattice3(A_13,B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0(A_13))
      | ~ l1_orders_2(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_144,plain,(
    ! [A_159,D_160,C_161,B_162] :
      ( r1_orders_2(A_159,D_160,C_161)
      | ~ r2_hidden(D_160,B_162)
      | ~ m1_subset_1(D_160,u1_struct_0(A_159))
      | ~ r2_lattice3(A_159,B_162,C_161)
      | ~ m1_subset_1(C_161,u1_struct_0(A_159))
      | ~ l1_orders_2(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_550,plain,(
    ! [B_327,C_326,A_329,A_328,C_325] :
      ( r1_orders_2(A_329,'#skF_2'(A_328,B_327,C_325),C_326)
      | ~ m1_subset_1('#skF_2'(A_328,B_327,C_325),u1_struct_0(A_329))
      | ~ r2_lattice3(A_329,B_327,C_326)
      | ~ m1_subset_1(C_326,u1_struct_0(A_329))
      | ~ l1_orders_2(A_329)
      | r2_lattice3(A_328,B_327,C_325)
      | ~ m1_subset_1(C_325,u1_struct_0(A_328))
      | ~ l1_orders_2(A_328) ) ),
    inference(resolution,[status(thm)],[c_14,c_144])).

tff(c_681,plain,(
    ! [C_357,A_356,C_359,B_358,A_360] :
      ( r1_orders_2(A_356,'#skF_2'(A_360,B_358,C_359),C_357)
      | ~ r2_lattice3(A_356,B_358,C_357)
      | ~ m1_subset_1(C_357,u1_struct_0(A_356))
      | ~ m1_yellow_0(A_360,A_356)
      | v2_struct_0(A_360)
      | ~ l1_orders_2(A_356)
      | v2_struct_0(A_356)
      | r2_lattice3(A_360,B_358,C_359)
      | ~ m1_subset_1(C_359,u1_struct_0(A_360))
      | ~ l1_orders_2(A_360) ) ),
    inference(resolution,[status(thm)],[c_136,c_550])).

tff(c_3028,plain,(
    ! [C_1018,B_1017,A_1016,A_1015,B_1013,C_1014] :
      ( r1_orders_2(B_1013,'#skF_2'(A_1016,B_1017,C_1014),C_1018)
      | ~ m1_subset_1(C_1018,u1_struct_0(B_1013))
      | ~ m1_subset_1('#skF_2'(A_1016,B_1017,C_1014),u1_struct_0(A_1015))
      | ~ m1_yellow_0(B_1013,A_1015)
      | ~ v4_yellow_0(B_1013,A_1015)
      | v1_xboole_0(u1_struct_0(B_1013))
      | ~ m1_subset_1('#skF_2'(A_1016,B_1017,C_1014),u1_struct_0(B_1013))
      | ~ r2_lattice3(A_1015,B_1017,C_1018)
      | ~ m1_subset_1(C_1018,u1_struct_0(A_1015))
      | ~ m1_yellow_0(A_1016,A_1015)
      | v2_struct_0(A_1016)
      | ~ l1_orders_2(A_1015)
      | v2_struct_0(A_1015)
      | r2_lattice3(A_1016,B_1017,C_1014)
      | ~ m1_subset_1(C_1014,u1_struct_0(A_1016))
      | ~ l1_orders_2(A_1016) ) ),
    inference(resolution,[status(thm)],[c_681,c_176])).

tff(c_5006,plain,(
    ! [C_1396,C_1394,A_1391,B_1393,B_1392,A_1395] :
      ( r1_orders_2(B_1393,'#skF_2'(A_1395,B_1392,C_1394),C_1396)
      | ~ m1_subset_1(C_1396,u1_struct_0(B_1393))
      | ~ m1_yellow_0(B_1393,A_1391)
      | ~ v4_yellow_0(B_1393,A_1391)
      | v1_xboole_0(u1_struct_0(B_1393))
      | ~ m1_subset_1('#skF_2'(A_1395,B_1392,C_1394),u1_struct_0(B_1393))
      | ~ r2_lattice3(A_1391,B_1392,C_1396)
      | ~ m1_subset_1(C_1396,u1_struct_0(A_1391))
      | ~ m1_yellow_0(A_1395,A_1391)
      | v2_struct_0(A_1395)
      | ~ l1_orders_2(A_1391)
      | v2_struct_0(A_1391)
      | r2_lattice3(A_1395,B_1392,C_1394)
      | ~ m1_subset_1(C_1394,u1_struct_0(A_1395))
      | ~ l1_orders_2(A_1395) ) ),
    inference(resolution,[status(thm)],[c_136,c_3028])).

tff(c_5008,plain,(
    ! [A_1395,B_1392,C_1394,C_1396] :
      ( r1_orders_2('#skF_4','#skF_2'(A_1395,B_1392,C_1394),C_1396)
      | ~ m1_subset_1(C_1396,u1_struct_0('#skF_4'))
      | ~ m1_yellow_0('#skF_4','#skF_3')
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_1395,B_1392,C_1394),u1_struct_0('#skF_4'))
      | ~ r2_lattice3('#skF_3',B_1392,C_1396)
      | ~ m1_subset_1(C_1396,u1_struct_0('#skF_3'))
      | ~ m1_yellow_0(A_1395,'#skF_3')
      | v2_struct_0(A_1395)
      | ~ l1_orders_2('#skF_3')
      | v2_struct_0('#skF_3')
      | r2_lattice3(A_1395,B_1392,C_1394)
      | ~ m1_subset_1(C_1394,u1_struct_0(A_1395))
      | ~ l1_orders_2(A_1395) ) ),
    inference(resolution,[status(thm)],[c_40,c_5006])).

tff(c_5011,plain,(
    ! [A_1395,B_1392,C_1394,C_1396] :
      ( r1_orders_2('#skF_4','#skF_2'(A_1395,B_1392,C_1394),C_1396)
      | ~ m1_subset_1(C_1396,u1_struct_0('#skF_4'))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_1395,B_1392,C_1394),u1_struct_0('#skF_4'))
      | ~ r2_lattice3('#skF_3',B_1392,C_1396)
      | ~ m1_subset_1(C_1396,u1_struct_0('#skF_3'))
      | ~ m1_yellow_0(A_1395,'#skF_3')
      | v2_struct_0(A_1395)
      | v2_struct_0('#skF_3')
      | r2_lattice3(A_1395,B_1392,C_1394)
      | ~ m1_subset_1(C_1394,u1_struct_0(A_1395))
      | ~ l1_orders_2(A_1395) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_38,c_5008])).

tff(c_5051,plain,(
    ! [A_1403,B_1404,C_1405,C_1406] :
      ( r1_orders_2('#skF_4','#skF_2'(A_1403,B_1404,C_1405),C_1406)
      | ~ m1_subset_1(C_1406,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_1403,B_1404,C_1405),u1_struct_0('#skF_4'))
      | ~ r2_lattice3('#skF_3',B_1404,C_1406)
      | ~ m1_subset_1(C_1406,u1_struct_0('#skF_3'))
      | ~ m1_yellow_0(A_1403,'#skF_3')
      | v2_struct_0(A_1403)
      | r2_lattice3(A_1403,B_1404,C_1405)
      | ~ m1_subset_1(C_1405,u1_struct_0(A_1403))
      | ~ l1_orders_2(A_1403) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_3646,c_5011])).

tff(c_5066,plain,(
    ! [B_20,C_21,C_1406] :
      ( r1_orders_2('#skF_4','#skF_2'('#skF_4',B_20,C_21),C_1406)
      | ~ m1_subset_1(C_1406,u1_struct_0('#skF_4'))
      | ~ r2_lattice3('#skF_3',B_20,C_1406)
      | ~ m1_subset_1(C_1406,u1_struct_0('#skF_3'))
      | ~ m1_yellow_0('#skF_4','#skF_3')
      | v2_struct_0('#skF_4')
      | r2_lattice3('#skF_4',B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_16,c_5051])).

tff(c_5088,plain,(
    ! [B_20,C_21,C_1406] :
      ( r1_orders_2('#skF_4','#skF_2'('#skF_4',B_20,C_21),C_1406)
      | ~ m1_subset_1(C_1406,u1_struct_0('#skF_4'))
      | ~ r2_lattice3('#skF_3',B_20,C_1406)
      | ~ m1_subset_1(C_1406,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_4')
      | r2_lattice3('#skF_4',B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_38,c_5066])).

tff(c_5091,plain,(
    ! [B_1407,C_1408,C_1409] :
      ( r1_orders_2('#skF_4','#skF_2'('#skF_4',B_1407,C_1408),C_1409)
      | ~ m1_subset_1(C_1409,u1_struct_0('#skF_4'))
      | ~ r2_lattice3('#skF_3',B_1407,C_1409)
      | ~ m1_subset_1(C_1409,u1_struct_0('#skF_3'))
      | r2_lattice3('#skF_4',B_1407,C_1408)
      | ~ m1_subset_1(C_1408,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_5088])).

tff(c_12,plain,(
    ! [A_13,B_20,C_21] :
      ( ~ r1_orders_2(A_13,'#skF_2'(A_13,B_20,C_21),C_21)
      | r2_lattice3(A_13,B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0(A_13))
      | ~ l1_orders_2(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_5104,plain,(
    ! [B_1407,C_1409] :
      ( ~ l1_orders_2('#skF_4')
      | ~ r2_lattice3('#skF_3',B_1407,C_1409)
      | ~ m1_subset_1(C_1409,u1_struct_0('#skF_3'))
      | r2_lattice3('#skF_4',B_1407,C_1409)
      | ~ m1_subset_1(C_1409,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_5091,c_12])).

tff(c_5117,plain,(
    ! [B_1410,C_1411] :
      ( ~ r2_lattice3('#skF_3',B_1410,C_1411)
      | ~ m1_subset_1(C_1411,u1_struct_0('#skF_3'))
      | r2_lattice3('#skF_4',B_1410,C_1411)
      | ~ m1_subset_1(C_1411,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_5104])).

tff(c_5125,plain,
    ( ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | r2_lattice3('#skF_4','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_64,c_5117])).

tff(c_5136,plain,(
    r2_lattice3('#skF_4','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_36,c_5125])).

tff(c_5138,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_5136])).

tff(c_5139,plain,(
    ~ r1_lattice3('#skF_4','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_5140,plain,(
    r2_lattice3('#skF_4','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_50,plain,
    ( r1_lattice3('#skF_3','#skF_5','#skF_6')
    | ~ r2_lattice3('#skF_4','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_55,plain,
    ( r1_lattice3('#skF_3','#skF_5','#skF_6')
    | ~ r2_lattice3('#skF_4','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_50])).

tff(c_5141,plain,(
    ~ r2_lattice3('#skF_4','#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_55])).

tff(c_5143,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5140,c_5141])).

tff(c_5144,plain,(
    r1_lattice3('#skF_3','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_55])).

tff(c_5168,plain,(
    ! [C_1438,A_1439,B_1440] :
      ( m1_subset_1(C_1438,u1_struct_0(A_1439))
      | ~ m1_subset_1(C_1438,u1_struct_0(B_1440))
      | ~ m1_yellow_0(B_1440,A_1439)
      | v2_struct_0(B_1440)
      | ~ l1_orders_2(A_1439)
      | v2_struct_0(A_1439) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_5184,plain,(
    ! [A_1,B_8,C_9,A_1439] :
      ( m1_subset_1('#skF_1'(A_1,B_8,C_9),u1_struct_0(A_1439))
      | ~ m1_yellow_0(A_1,A_1439)
      | v2_struct_0(A_1)
      | ~ l1_orders_2(A_1439)
      | v2_struct_0(A_1439)
      | r1_lattice3(A_1,B_8,C_9)
      | ~ m1_subset_1(C_9,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(resolution,[status(thm)],[c_8,c_5168])).

tff(c_5215,plain,(
    ! [A_1447,C_1448,D_1449,B_1450] :
      ( r1_orders_2(A_1447,C_1448,D_1449)
      | ~ r2_hidden(D_1449,B_1450)
      | ~ m1_subset_1(D_1449,u1_struct_0(A_1447))
      | ~ r1_lattice3(A_1447,B_1450,C_1448)
      | ~ m1_subset_1(C_1448,u1_struct_0(A_1447))
      | ~ l1_orders_2(A_1447) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_5627,plain,(
    ! [A_1591,A_1595,C_1593,C_1594,B_1592] :
      ( r1_orders_2(A_1591,C_1594,'#skF_1'(A_1595,B_1592,C_1593))
      | ~ m1_subset_1('#skF_1'(A_1595,B_1592,C_1593),u1_struct_0(A_1591))
      | ~ r1_lattice3(A_1591,B_1592,C_1594)
      | ~ m1_subset_1(C_1594,u1_struct_0(A_1591))
      | ~ l1_orders_2(A_1591)
      | r1_lattice3(A_1595,B_1592,C_1593)
      | ~ m1_subset_1(C_1593,u1_struct_0(A_1595))
      | ~ l1_orders_2(A_1595) ) ),
    inference(resolution,[status(thm)],[c_6,c_5215])).

tff(c_5646,plain,(
    ! [A_1,C_1594,A_1439,B_8,C_9] :
      ( r1_orders_2(A_1439,C_1594,'#skF_1'(A_1,B_8,C_9))
      | ~ r1_lattice3(A_1439,B_8,C_1594)
      | ~ m1_subset_1(C_1594,u1_struct_0(A_1439))
      | ~ m1_yellow_0(A_1,A_1439)
      | v2_struct_0(A_1)
      | ~ l1_orders_2(A_1439)
      | v2_struct_0(A_1439)
      | r1_lattice3(A_1,B_8,C_9)
      | ~ m1_subset_1(C_9,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(resolution,[status(thm)],[c_5184,c_5627])).

tff(c_5272,plain,(
    ! [B_1461,E_1462,F_1463,A_1464] :
      ( r1_orders_2(B_1461,E_1462,F_1463)
      | ~ r2_hidden(E_1462,u1_struct_0(B_1461))
      | ~ r1_orders_2(A_1464,E_1462,F_1463)
      | ~ m1_subset_1(F_1463,u1_struct_0(B_1461))
      | ~ m1_subset_1(E_1462,u1_struct_0(B_1461))
      | ~ m1_subset_1(F_1463,u1_struct_0(A_1464))
      | ~ m1_subset_1(E_1462,u1_struct_0(A_1464))
      | ~ m1_yellow_0(B_1461,A_1464)
      | ~ v4_yellow_0(B_1461,A_1464)
      | ~ l1_orders_2(A_1464) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_5769,plain,(
    ! [B_1650,A_1651,F_1652,A_1653] :
      ( r1_orders_2(B_1650,A_1651,F_1652)
      | ~ r1_orders_2(A_1653,A_1651,F_1652)
      | ~ m1_subset_1(F_1652,u1_struct_0(B_1650))
      | ~ m1_subset_1(F_1652,u1_struct_0(A_1653))
      | ~ m1_subset_1(A_1651,u1_struct_0(A_1653))
      | ~ m1_yellow_0(B_1650,A_1653)
      | ~ v4_yellow_0(B_1650,A_1653)
      | ~ l1_orders_2(A_1653)
      | v1_xboole_0(u1_struct_0(B_1650))
      | ~ m1_subset_1(A_1651,u1_struct_0(B_1650)) ) ),
    inference(resolution,[status(thm)],[c_26,c_5272])).

tff(c_8339,plain,(
    ! [A_2329,C_2328,B_2326,C_2327,B_2331,A_2330] :
      ( r1_orders_2(B_2331,C_2327,'#skF_1'(A_2330,B_2326,C_2328))
      | ~ m1_subset_1('#skF_1'(A_2330,B_2326,C_2328),u1_struct_0(B_2331))
      | ~ m1_subset_1('#skF_1'(A_2330,B_2326,C_2328),u1_struct_0(A_2329))
      | ~ m1_yellow_0(B_2331,A_2329)
      | ~ v4_yellow_0(B_2331,A_2329)
      | v1_xboole_0(u1_struct_0(B_2331))
      | ~ m1_subset_1(C_2327,u1_struct_0(B_2331))
      | ~ r1_lattice3(A_2329,B_2326,C_2327)
      | ~ m1_subset_1(C_2327,u1_struct_0(A_2329))
      | ~ m1_yellow_0(A_2330,A_2329)
      | v2_struct_0(A_2330)
      | ~ l1_orders_2(A_2329)
      | v2_struct_0(A_2329)
      | r1_lattice3(A_2330,B_2326,C_2328)
      | ~ m1_subset_1(C_2328,u1_struct_0(A_2330))
      | ~ l1_orders_2(A_2330) ) ),
    inference(resolution,[status(thm)],[c_5646,c_5769])).

tff(c_8413,plain,(
    ! [C_2341,A_2344,B_2342,C_2343,A_2345] :
      ( r1_orders_2(A_2345,C_2341,'#skF_1'(A_2345,B_2342,C_2343))
      | ~ m1_subset_1('#skF_1'(A_2345,B_2342,C_2343),u1_struct_0(A_2344))
      | ~ v4_yellow_0(A_2345,A_2344)
      | v1_xboole_0(u1_struct_0(A_2345))
      | ~ m1_subset_1(C_2341,u1_struct_0(A_2345))
      | ~ r1_lattice3(A_2344,B_2342,C_2341)
      | ~ m1_subset_1(C_2341,u1_struct_0(A_2344))
      | ~ m1_yellow_0(A_2345,A_2344)
      | v2_struct_0(A_2345)
      | ~ l1_orders_2(A_2344)
      | v2_struct_0(A_2344)
      | r1_lattice3(A_2345,B_2342,C_2343)
      | ~ m1_subset_1(C_2343,u1_struct_0(A_2345))
      | ~ l1_orders_2(A_2345) ) ),
    inference(resolution,[status(thm)],[c_8,c_8339])).

tff(c_8802,plain,(
    ! [A_2374,C_2372,C_2375,B_2371,A_2373] :
      ( r1_orders_2(A_2374,C_2375,'#skF_1'(A_2374,B_2371,C_2372))
      | ~ v4_yellow_0(A_2374,A_2373)
      | v1_xboole_0(u1_struct_0(A_2374))
      | ~ m1_subset_1(C_2375,u1_struct_0(A_2374))
      | ~ r1_lattice3(A_2373,B_2371,C_2375)
      | ~ m1_subset_1(C_2375,u1_struct_0(A_2373))
      | ~ m1_yellow_0(A_2374,A_2373)
      | v2_struct_0(A_2374)
      | ~ l1_orders_2(A_2373)
      | v2_struct_0(A_2373)
      | r1_lattice3(A_2374,B_2371,C_2372)
      | ~ m1_subset_1(C_2372,u1_struct_0(A_2374))
      | ~ l1_orders_2(A_2374) ) ),
    inference(resolution,[status(thm)],[c_5184,c_8413])).

tff(c_8804,plain,(
    ! [C_2375,B_2371,C_2372] :
      ( r1_orders_2('#skF_4',C_2375,'#skF_1'('#skF_4',B_2371,C_2372))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_2375,u1_struct_0('#skF_4'))
      | ~ r1_lattice3('#skF_3',B_2371,C_2375)
      | ~ m1_subset_1(C_2375,u1_struct_0('#skF_3'))
      | ~ m1_yellow_0('#skF_4','#skF_3')
      | v2_struct_0('#skF_4')
      | ~ l1_orders_2('#skF_3')
      | v2_struct_0('#skF_3')
      | r1_lattice3('#skF_4',B_2371,C_2372)
      | ~ m1_subset_1(C_2372,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40,c_8802])).

tff(c_8807,plain,(
    ! [C_2375,B_2371,C_2372] :
      ( r1_orders_2('#skF_4',C_2375,'#skF_1'('#skF_4',B_2371,C_2372))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_2375,u1_struct_0('#skF_4'))
      | ~ r1_lattice3('#skF_3',B_2371,C_2375)
      | ~ m1_subset_1(C_2375,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | r1_lattice3('#skF_4',B_2371,C_2372)
      | ~ m1_subset_1(C_2372,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_44,c_38,c_8804])).

tff(c_8808,plain,(
    ! [C_2375,B_2371,C_2372] :
      ( r1_orders_2('#skF_4',C_2375,'#skF_1'('#skF_4',B_2371,C_2372))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_2375,u1_struct_0('#skF_4'))
      | ~ r1_lattice3('#skF_3',B_2371,C_2375)
      | ~ m1_subset_1(C_2375,u1_struct_0('#skF_3'))
      | r1_lattice3('#skF_4',B_2371,C_2372)
      | ~ m1_subset_1(C_2372,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_42,c_8807])).

tff(c_8839,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_8808])).

tff(c_8842,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_8839,c_22])).

tff(c_8845,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_8842])).

tff(c_8848,plain,(
    ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_8845])).

tff(c_8852,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_8848])).

tff(c_8897,plain,(
    ! [C_2387,B_2388,C_2389] :
      ( r1_orders_2('#skF_4',C_2387,'#skF_1'('#skF_4',B_2388,C_2389))
      | ~ m1_subset_1(C_2387,u1_struct_0('#skF_4'))
      | ~ r1_lattice3('#skF_3',B_2388,C_2387)
      | ~ m1_subset_1(C_2387,u1_struct_0('#skF_3'))
      | r1_lattice3('#skF_4',B_2388,C_2389)
      | ~ m1_subset_1(C_2389,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_8808])).

tff(c_4,plain,(
    ! [A_1,C_9,B_8] :
      ( ~ r1_orders_2(A_1,C_9,'#skF_1'(A_1,B_8,C_9))
      | r1_lattice3(A_1,B_8,C_9)
      | ~ m1_subset_1(C_9,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8913,plain,(
    ! [B_2388,C_2389] :
      ( ~ l1_orders_2('#skF_4')
      | ~ r1_lattice3('#skF_3',B_2388,C_2389)
      | ~ m1_subset_1(C_2389,u1_struct_0('#skF_3'))
      | r1_lattice3('#skF_4',B_2388,C_2389)
      | ~ m1_subset_1(C_2389,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_8897,c_4])).

tff(c_8929,plain,(
    ! [B_2390,C_2391] :
      ( ~ r1_lattice3('#skF_3',B_2390,C_2391)
      | ~ m1_subset_1(C_2391,u1_struct_0('#skF_3'))
      | r1_lattice3('#skF_4',B_2390,C_2391)
      | ~ m1_subset_1(C_2391,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_8913])).

tff(c_8937,plain,
    ( ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | r1_lattice3('#skF_4','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_5144,c_8929])).

tff(c_8948,plain,(
    r1_lattice3('#skF_4','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_36,c_8937])).

tff(c_8950,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5139,c_8948])).

tff(c_8952,plain,(
    ~ r2_lattice3('#skF_3','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_52,plain,
    ( ~ r1_lattice3('#skF_4','#skF_5','#skF_7')
    | r2_lattice3('#skF_3','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_57,plain,
    ( ~ r1_lattice3('#skF_4','#skF_5','#skF_6')
    | r2_lattice3('#skF_3','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_52])).

tff(c_8963,plain,(
    ~ r1_lattice3('#skF_4','#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_8952,c_57])).

tff(c_8951,plain,(
    r1_lattice3('#skF_3','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_8955,plain,(
    ! [B_2395,A_2396] :
      ( l1_orders_2(B_2395)
      | ~ m1_yellow_0(B_2395,A_2396)
      | ~ l1_orders_2(A_2396) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_8958,plain,
    ( l1_orders_2('#skF_4')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_8955])).

tff(c_8961,plain,(
    l1_orders_2('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_8958])).

tff(c_9014,plain,(
    ! [A_2425,B_2426,C_2427] :
      ( m1_subset_1('#skF_2'(A_2425,B_2426,C_2427),u1_struct_0(A_2425))
      | r2_lattice3(A_2425,B_2426,C_2427)
      | ~ m1_subset_1(C_2427,u1_struct_0(A_2425))
      | ~ l1_orders_2(A_2425) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_9017,plain,(
    ! [A_2425,B_2426,C_2427,A_34] :
      ( m1_subset_1('#skF_2'(A_2425,B_2426,C_2427),u1_struct_0(A_34))
      | ~ m1_yellow_0(A_2425,A_34)
      | v2_struct_0(A_2425)
      | ~ l1_orders_2(A_34)
      | v2_struct_0(A_34)
      | r2_lattice3(A_2425,B_2426,C_2427)
      | ~ m1_subset_1(C_2427,u1_struct_0(A_2425))
      | ~ l1_orders_2(A_2425) ) ),
    inference(resolution,[status(thm)],[c_9014,c_28])).

tff(c_9042,plain,(
    ! [A_2436,C_2437,D_2438,B_2439] :
      ( r1_orders_2(A_2436,C_2437,D_2438)
      | ~ r2_hidden(D_2438,B_2439)
      | ~ m1_subset_1(D_2438,u1_struct_0(A_2436))
      | ~ r1_lattice3(A_2436,B_2439,C_2437)
      | ~ m1_subset_1(C_2437,u1_struct_0(A_2436))
      | ~ l1_orders_2(A_2436) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_9443,plain,(
    ! [A_2591,B_2590,A_2592,C_2588,C_2589] :
      ( r1_orders_2(A_2591,C_2589,'#skF_2'(A_2592,B_2590,C_2588))
      | ~ m1_subset_1('#skF_2'(A_2592,B_2590,C_2588),u1_struct_0(A_2591))
      | ~ r1_lattice3(A_2591,B_2590,C_2589)
      | ~ m1_subset_1(C_2589,u1_struct_0(A_2591))
      | ~ l1_orders_2(A_2591)
      | r2_lattice3(A_2592,B_2590,C_2588)
      | ~ m1_subset_1(C_2588,u1_struct_0(A_2592))
      | ~ l1_orders_2(A_2592) ) ),
    inference(resolution,[status(thm)],[c_14,c_9042])).

tff(c_9553,plain,(
    ! [A_2620,C_2622,B_2621,C_2619,A_2623] :
      ( r1_orders_2(A_2620,C_2619,'#skF_2'(A_2623,B_2621,C_2622))
      | ~ r1_lattice3(A_2620,B_2621,C_2619)
      | ~ m1_subset_1(C_2619,u1_struct_0(A_2620))
      | ~ m1_yellow_0(A_2623,A_2620)
      | v2_struct_0(A_2623)
      | ~ l1_orders_2(A_2620)
      | v2_struct_0(A_2620)
      | r2_lattice3(A_2623,B_2621,C_2622)
      | ~ m1_subset_1(C_2622,u1_struct_0(A_2623))
      | ~ l1_orders_2(A_2623) ) ),
    inference(resolution,[status(thm)],[c_9017,c_9443])).

tff(c_9123,plain,(
    ! [B_2454,E_2455,F_2456,A_2457] :
      ( r1_orders_2(B_2454,E_2455,F_2456)
      | ~ r2_hidden(E_2455,u1_struct_0(B_2454))
      | ~ r1_orders_2(A_2457,E_2455,F_2456)
      | ~ m1_subset_1(F_2456,u1_struct_0(B_2454))
      | ~ m1_subset_1(E_2455,u1_struct_0(B_2454))
      | ~ m1_subset_1(F_2456,u1_struct_0(A_2457))
      | ~ m1_subset_1(E_2455,u1_struct_0(A_2457))
      | ~ m1_yellow_0(B_2454,A_2457)
      | ~ v4_yellow_0(B_2454,A_2457)
      | ~ l1_orders_2(A_2457) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_9135,plain,(
    ! [B_2454,A_32,F_2456,A_2457] :
      ( r1_orders_2(B_2454,A_32,F_2456)
      | ~ r1_orders_2(A_2457,A_32,F_2456)
      | ~ m1_subset_1(F_2456,u1_struct_0(B_2454))
      | ~ m1_subset_1(F_2456,u1_struct_0(A_2457))
      | ~ m1_subset_1(A_32,u1_struct_0(A_2457))
      | ~ m1_yellow_0(B_2454,A_2457)
      | ~ v4_yellow_0(B_2454,A_2457)
      | ~ l1_orders_2(A_2457)
      | v1_xboole_0(u1_struct_0(B_2454))
      | ~ m1_subset_1(A_32,u1_struct_0(B_2454)) ) ),
    inference(resolution,[status(thm)],[c_26,c_9123])).

tff(c_11906,plain,(
    ! [B_3292,A_3287,A_3291,C_3290,B_3288,C_3289] :
      ( r1_orders_2(B_3288,C_3289,'#skF_2'(A_3287,B_3292,C_3290))
      | ~ m1_subset_1('#skF_2'(A_3287,B_3292,C_3290),u1_struct_0(B_3288))
      | ~ m1_subset_1('#skF_2'(A_3287,B_3292,C_3290),u1_struct_0(A_3291))
      | ~ m1_yellow_0(B_3288,A_3291)
      | ~ v4_yellow_0(B_3288,A_3291)
      | v1_xboole_0(u1_struct_0(B_3288))
      | ~ m1_subset_1(C_3289,u1_struct_0(B_3288))
      | ~ r1_lattice3(A_3291,B_3292,C_3289)
      | ~ m1_subset_1(C_3289,u1_struct_0(A_3291))
      | ~ m1_yellow_0(A_3287,A_3291)
      | v2_struct_0(A_3287)
      | ~ l1_orders_2(A_3291)
      | v2_struct_0(A_3291)
      | r2_lattice3(A_3287,B_3292,C_3290)
      | ~ m1_subset_1(C_3290,u1_struct_0(A_3287))
      | ~ l1_orders_2(A_3287) ) ),
    inference(resolution,[status(thm)],[c_9553,c_9135])).

tff(c_11936,plain,(
    ! [C_3293,C_3294,A_3297,A_3296,B_3295] :
      ( r1_orders_2(A_3296,C_3294,'#skF_2'(A_3296,B_3295,C_3293))
      | ~ m1_subset_1('#skF_2'(A_3296,B_3295,C_3293),u1_struct_0(A_3297))
      | ~ v4_yellow_0(A_3296,A_3297)
      | v1_xboole_0(u1_struct_0(A_3296))
      | ~ m1_subset_1(C_3294,u1_struct_0(A_3296))
      | ~ r1_lattice3(A_3297,B_3295,C_3294)
      | ~ m1_subset_1(C_3294,u1_struct_0(A_3297))
      | ~ m1_yellow_0(A_3296,A_3297)
      | v2_struct_0(A_3296)
      | ~ l1_orders_2(A_3297)
      | v2_struct_0(A_3297)
      | r2_lattice3(A_3296,B_3295,C_3293)
      | ~ m1_subset_1(C_3293,u1_struct_0(A_3296))
      | ~ l1_orders_2(A_3296) ) ),
    inference(resolution,[status(thm)],[c_16,c_11906])).

tff(c_11985,plain,(
    ! [C_3305,C_3304,A_3302,A_3306,B_3303] :
      ( r1_orders_2(A_3306,C_3304,'#skF_2'(A_3306,B_3303,C_3305))
      | ~ v4_yellow_0(A_3306,A_3302)
      | v1_xboole_0(u1_struct_0(A_3306))
      | ~ m1_subset_1(C_3304,u1_struct_0(A_3306))
      | ~ r1_lattice3(A_3302,B_3303,C_3304)
      | ~ m1_subset_1(C_3304,u1_struct_0(A_3302))
      | ~ m1_yellow_0(A_3306,A_3302)
      | v2_struct_0(A_3306)
      | ~ l1_orders_2(A_3302)
      | v2_struct_0(A_3302)
      | r2_lattice3(A_3306,B_3303,C_3305)
      | ~ m1_subset_1(C_3305,u1_struct_0(A_3306))
      | ~ l1_orders_2(A_3306) ) ),
    inference(resolution,[status(thm)],[c_9017,c_11936])).

tff(c_11987,plain,(
    ! [C_3304,B_3303,C_3305] :
      ( r1_orders_2('#skF_4',C_3304,'#skF_2'('#skF_4',B_3303,C_3305))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_3304,u1_struct_0('#skF_4'))
      | ~ r1_lattice3('#skF_3',B_3303,C_3304)
      | ~ m1_subset_1(C_3304,u1_struct_0('#skF_3'))
      | ~ m1_yellow_0('#skF_4','#skF_3')
      | v2_struct_0('#skF_4')
      | ~ l1_orders_2('#skF_3')
      | v2_struct_0('#skF_3')
      | r2_lattice3('#skF_4',B_3303,C_3305)
      | ~ m1_subset_1(C_3305,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40,c_11985])).

tff(c_11990,plain,(
    ! [C_3304,B_3303,C_3305] :
      ( r1_orders_2('#skF_4',C_3304,'#skF_2'('#skF_4',B_3303,C_3305))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_3304,u1_struct_0('#skF_4'))
      | ~ r1_lattice3('#skF_3',B_3303,C_3304)
      | ~ m1_subset_1(C_3304,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | r2_lattice3('#skF_4',B_3303,C_3305)
      | ~ m1_subset_1(C_3305,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8961,c_44,c_38,c_11987])).

tff(c_11991,plain,(
    ! [C_3304,B_3303,C_3305] :
      ( r1_orders_2('#skF_4',C_3304,'#skF_2'('#skF_4',B_3303,C_3305))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_3304,u1_struct_0('#skF_4'))
      | ~ r1_lattice3('#skF_3',B_3303,C_3304)
      | ~ m1_subset_1(C_3304,u1_struct_0('#skF_3'))
      | r2_lattice3('#skF_4',B_3303,C_3305)
      | ~ m1_subset_1(C_3305,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_42,c_11990])).

tff(c_11992,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_11991])).

tff(c_11995,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_11992,c_22])).

tff(c_11998,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_11995])).

tff(c_12001,plain,(
    ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_11998])).

tff(c_12005,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8961,c_12001])).

tff(c_12007,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_11991])).

tff(c_8983,plain,(
    ! [C_2417,A_2418,B_2419] :
      ( m1_subset_1(C_2417,u1_struct_0(A_2418))
      | ~ m1_subset_1(C_2417,u1_struct_0(B_2419))
      | ~ m1_yellow_0(B_2419,A_2418)
      | v2_struct_0(B_2419)
      | ~ l1_orders_2(A_2418)
      | v2_struct_0(A_2418) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_8996,plain,(
    ! [A_1,B_8,C_9,A_2418] :
      ( m1_subset_1('#skF_1'(A_1,B_8,C_9),u1_struct_0(A_2418))
      | ~ m1_yellow_0(A_1,A_2418)
      | v2_struct_0(A_1)
      | ~ l1_orders_2(A_2418)
      | v2_struct_0(A_2418)
      | r1_lattice3(A_1,B_8,C_9)
      | ~ m1_subset_1(C_9,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(resolution,[status(thm)],[c_8,c_8983])).

tff(c_9193,plain,(
    ! [B_2489,C_2490,C_2488,A_2492,A_2491] :
      ( r1_orders_2(A_2491,C_2488,'#skF_1'(A_2492,B_2489,C_2490))
      | ~ m1_subset_1('#skF_1'(A_2492,B_2489,C_2490),u1_struct_0(A_2491))
      | ~ r1_lattice3(A_2491,B_2489,C_2488)
      | ~ m1_subset_1(C_2488,u1_struct_0(A_2491))
      | ~ l1_orders_2(A_2491)
      | r1_lattice3(A_2492,B_2489,C_2490)
      | ~ m1_subset_1(C_2490,u1_struct_0(A_2492))
      | ~ l1_orders_2(A_2492) ) ),
    inference(resolution,[status(thm)],[c_6,c_9042])).

tff(c_9562,plain,(
    ! [C_2627,A_2624,A_2628,B_2625,C_2626] :
      ( r1_orders_2(A_2624,C_2627,'#skF_1'(A_2628,B_2625,C_2626))
      | ~ r1_lattice3(A_2624,B_2625,C_2627)
      | ~ m1_subset_1(C_2627,u1_struct_0(A_2624))
      | ~ m1_yellow_0(A_2628,A_2624)
      | v2_struct_0(A_2628)
      | ~ l1_orders_2(A_2624)
      | v2_struct_0(A_2624)
      | r1_lattice3(A_2628,B_2625,C_2626)
      | ~ m1_subset_1(C_2626,u1_struct_0(A_2628))
      | ~ l1_orders_2(A_2628) ) ),
    inference(resolution,[status(thm)],[c_8996,c_9193])).

tff(c_12138,plain,(
    ! [C_3349,A_3350,A_3348,C_3347,B_3346,B_3351] :
      ( r1_orders_2(B_3346,C_3349,'#skF_1'(A_3350,B_3351,C_3347))
      | ~ m1_subset_1('#skF_1'(A_3350,B_3351,C_3347),u1_struct_0(B_3346))
      | ~ m1_subset_1('#skF_1'(A_3350,B_3351,C_3347),u1_struct_0(A_3348))
      | ~ m1_yellow_0(B_3346,A_3348)
      | ~ v4_yellow_0(B_3346,A_3348)
      | v1_xboole_0(u1_struct_0(B_3346))
      | ~ m1_subset_1(C_3349,u1_struct_0(B_3346))
      | ~ r1_lattice3(A_3348,B_3351,C_3349)
      | ~ m1_subset_1(C_3349,u1_struct_0(A_3348))
      | ~ m1_yellow_0(A_3350,A_3348)
      | v2_struct_0(A_3350)
      | ~ l1_orders_2(A_3348)
      | v2_struct_0(A_3348)
      | r1_lattice3(A_3350,B_3351,C_3347)
      | ~ m1_subset_1(C_3347,u1_struct_0(A_3350))
      | ~ l1_orders_2(A_3350) ) ),
    inference(resolution,[status(thm)],[c_9562,c_9135])).

tff(c_12168,plain,(
    ! [B_3352,A_3354,C_3353,A_3356,C_3355] :
      ( r1_orders_2(A_3356,C_3355,'#skF_1'(A_3356,B_3352,C_3353))
      | ~ m1_subset_1('#skF_1'(A_3356,B_3352,C_3353),u1_struct_0(A_3354))
      | ~ v4_yellow_0(A_3356,A_3354)
      | v1_xboole_0(u1_struct_0(A_3356))
      | ~ m1_subset_1(C_3355,u1_struct_0(A_3356))
      | ~ r1_lattice3(A_3354,B_3352,C_3355)
      | ~ m1_subset_1(C_3355,u1_struct_0(A_3354))
      | ~ m1_yellow_0(A_3356,A_3354)
      | v2_struct_0(A_3356)
      | ~ l1_orders_2(A_3354)
      | v2_struct_0(A_3354)
      | r1_lattice3(A_3356,B_3352,C_3353)
      | ~ m1_subset_1(C_3353,u1_struct_0(A_3356))
      | ~ l1_orders_2(A_3356) ) ),
    inference(resolution,[status(thm)],[c_8,c_12138])).

tff(c_12570,plain,(
    ! [A_3386,C_3383,A_3382,B_3384,C_3385] :
      ( r1_orders_2(A_3386,C_3383,'#skF_1'(A_3386,B_3384,C_3385))
      | ~ v4_yellow_0(A_3386,A_3382)
      | v1_xboole_0(u1_struct_0(A_3386))
      | ~ m1_subset_1(C_3383,u1_struct_0(A_3386))
      | ~ r1_lattice3(A_3382,B_3384,C_3383)
      | ~ m1_subset_1(C_3383,u1_struct_0(A_3382))
      | ~ m1_yellow_0(A_3386,A_3382)
      | v2_struct_0(A_3386)
      | ~ l1_orders_2(A_3382)
      | v2_struct_0(A_3382)
      | r1_lattice3(A_3386,B_3384,C_3385)
      | ~ m1_subset_1(C_3385,u1_struct_0(A_3386))
      | ~ l1_orders_2(A_3386) ) ),
    inference(resolution,[status(thm)],[c_8996,c_12168])).

tff(c_12572,plain,(
    ! [C_3383,B_3384,C_3385] :
      ( r1_orders_2('#skF_4',C_3383,'#skF_1'('#skF_4',B_3384,C_3385))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_3383,u1_struct_0('#skF_4'))
      | ~ r1_lattice3('#skF_3',B_3384,C_3383)
      | ~ m1_subset_1(C_3383,u1_struct_0('#skF_3'))
      | ~ m1_yellow_0('#skF_4','#skF_3')
      | v2_struct_0('#skF_4')
      | ~ l1_orders_2('#skF_3')
      | v2_struct_0('#skF_3')
      | r1_lattice3('#skF_4',B_3384,C_3385)
      | ~ m1_subset_1(C_3385,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40,c_12570])).

tff(c_12575,plain,(
    ! [C_3383,B_3384,C_3385] :
      ( r1_orders_2('#skF_4',C_3383,'#skF_1'('#skF_4',B_3384,C_3385))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_3383,u1_struct_0('#skF_4'))
      | ~ r1_lattice3('#skF_3',B_3384,C_3383)
      | ~ m1_subset_1(C_3383,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | r1_lattice3('#skF_4',B_3384,C_3385)
      | ~ m1_subset_1(C_3385,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8961,c_44,c_38,c_12572])).

tff(c_12577,plain,(
    ! [C_3387,B_3388,C_3389] :
      ( r1_orders_2('#skF_4',C_3387,'#skF_1'('#skF_4',B_3388,C_3389))
      | ~ m1_subset_1(C_3387,u1_struct_0('#skF_4'))
      | ~ r1_lattice3('#skF_3',B_3388,C_3387)
      | ~ m1_subset_1(C_3387,u1_struct_0('#skF_3'))
      | r1_lattice3('#skF_4',B_3388,C_3389)
      | ~ m1_subset_1(C_3389,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_42,c_12007,c_12575])).

tff(c_12589,plain,(
    ! [B_3388,C_3389] :
      ( ~ l1_orders_2('#skF_4')
      | ~ r1_lattice3('#skF_3',B_3388,C_3389)
      | ~ m1_subset_1(C_3389,u1_struct_0('#skF_3'))
      | r1_lattice3('#skF_4',B_3388,C_3389)
      | ~ m1_subset_1(C_3389,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_12577,c_4])).

tff(c_12609,plain,(
    ! [B_3390,C_3391] :
      ( ~ r1_lattice3('#skF_3',B_3390,C_3391)
      | ~ m1_subset_1(C_3391,u1_struct_0('#skF_3'))
      | r1_lattice3('#skF_4',B_3390,C_3391)
      | ~ m1_subset_1(C_3391,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8961,c_12589])).

tff(c_12617,plain,
    ( ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | r1_lattice3('#skF_4','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_8951,c_12609])).

tff(c_12628,plain,(
    r1_lattice3('#skF_4','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_36,c_12617])).

tff(c_12630,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8963,c_12628])).

%------------------------------------------------------------------------------
