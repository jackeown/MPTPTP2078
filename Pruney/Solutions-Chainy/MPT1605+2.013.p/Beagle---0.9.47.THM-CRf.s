%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:27 EST 2020

% Result     : Theorem 12.05s
% Output     : CNFRefutation 12.14s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 862 expanded)
%              Number of leaves         :   45 ( 318 expanded)
%              Depth                    :   20
%              Number of atoms          :  467 (2104 expanded)
%              Number of equality atoms :   16 ( 301 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r1_orders_2 > r1_lattice3 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k3_yellow_0 > k2_yellow_1 > k1_yellow_1 > k1_xboole_0 > #skF_4 > #skF_1 > #skF_5 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(k3_yellow_0,type,(
    k3_yellow_0: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v1_yellow_0,type,(
    v1_yellow_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_162,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ( r2_hidden(k1_xboole_0,A)
         => k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_121,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_141,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_90,axiom,(
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

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_129,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & v3_orders_2(k2_yellow_1(A))
      & v4_orders_2(k2_yellow_1(A))
      & v5_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).

tff(f_154,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
             => ( r3_orders_2(k2_yellow_1(A),B,C)
              <=> r1_tarski(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_yellow_0(A)
      <=> ? [B] :
            ( m1_subset_1(B,u1_struct_0(A))
            & r1_lattice3(A,u1_struct_0(A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_yellow_0)).

tff(f_137,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( ~ v2_struct_0(k2_yellow_1(A))
        & v1_orders_2(k2_yellow_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_yellow_1)).

tff(f_103,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(k3_yellow_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_44,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_117,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r1_orders_2(A,k3_yellow_0(A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_yellow_0)).

tff(c_76,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_72,plain,(
    k3_yellow_0(k2_yellow_1('#skF_5')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_74,plain,(
    r2_hidden(k1_xboole_0,'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_123,plain,(
    ! [A_63,B_64] :
      ( m1_subset_1(A_63,B_64)
      | ~ r2_hidden(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_131,plain,(
    m1_subset_1(k1_xboole_0,'#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_123])).

tff(c_50,plain,(
    ! [A_39] : l1_orders_2(k2_yellow_1(A_39)) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_64,plain,(
    ! [A_42] : u1_struct_0(k2_yellow_1(A_42)) = A_42 ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_8616,plain,(
    ! [A_1133,B_1134,C_1135] :
      ( r2_hidden('#skF_3'(A_1133,B_1134,C_1135),B_1134)
      | r1_lattice3(A_1133,B_1134,C_1135)
      | ~ m1_subset_1(C_1135,u1_struct_0(A_1133))
      | ~ l1_orders_2(A_1133) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_24,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,B_15)
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_8626,plain,(
    ! [A_1133,B_1134,C_1135] :
      ( m1_subset_1('#skF_3'(A_1133,B_1134,C_1135),B_1134)
      | r1_lattice3(A_1133,B_1134,C_1135)
      | ~ m1_subset_1(C_1135,u1_struct_0(A_1133))
      | ~ l1_orders_2(A_1133) ) ),
    inference(resolution,[status(thm)],[c_8616,c_24])).

tff(c_12,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_54,plain,(
    ! [A_40] : v3_orders_2(k2_yellow_1(A_40)) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_68,plain,(
    ! [A_43,B_47,C_49] :
      ( r3_orders_2(k2_yellow_1(A_43),B_47,C_49)
      | ~ r1_tarski(B_47,C_49)
      | ~ m1_subset_1(C_49,u1_struct_0(k2_yellow_1(A_43)))
      | ~ m1_subset_1(B_47,u1_struct_0(k2_yellow_1(A_43)))
      | v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_78,plain,(
    ! [A_43,B_47,C_49] :
      ( r3_orders_2(k2_yellow_1(A_43),B_47,C_49)
      | ~ r1_tarski(B_47,C_49)
      | ~ m1_subset_1(C_49,A_43)
      | ~ m1_subset_1(B_47,A_43)
      | v1_xboole_0(A_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_64,c_68])).

tff(c_9091,plain,(
    ! [A_1213,B_1214,C_1215] :
      ( r1_orders_2(A_1213,B_1214,C_1215)
      | ~ r3_orders_2(A_1213,B_1214,C_1215)
      | ~ m1_subset_1(C_1215,u1_struct_0(A_1213))
      | ~ m1_subset_1(B_1214,u1_struct_0(A_1213))
      | ~ l1_orders_2(A_1213)
      | ~ v3_orders_2(A_1213)
      | v2_struct_0(A_1213) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_9093,plain,(
    ! [A_43,B_47,C_49] :
      ( r1_orders_2(k2_yellow_1(A_43),B_47,C_49)
      | ~ m1_subset_1(C_49,u1_struct_0(k2_yellow_1(A_43)))
      | ~ m1_subset_1(B_47,u1_struct_0(k2_yellow_1(A_43)))
      | ~ l1_orders_2(k2_yellow_1(A_43))
      | ~ v3_orders_2(k2_yellow_1(A_43))
      | v2_struct_0(k2_yellow_1(A_43))
      | ~ r1_tarski(B_47,C_49)
      | ~ m1_subset_1(C_49,A_43)
      | ~ m1_subset_1(B_47,A_43)
      | v1_xboole_0(A_43) ) ),
    inference(resolution,[status(thm)],[c_78,c_9091])).

tff(c_10022,plain,(
    ! [A_1332,B_1333,C_1334] :
      ( r1_orders_2(k2_yellow_1(A_1332),B_1333,C_1334)
      | v2_struct_0(k2_yellow_1(A_1332))
      | ~ r1_tarski(B_1333,C_1334)
      | ~ m1_subset_1(C_1334,A_1332)
      | ~ m1_subset_1(B_1333,A_1332)
      | v1_xboole_0(A_1332) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_64,c_64,c_9093])).

tff(c_32,plain,(
    ! [A_19,C_27,B_26] :
      ( ~ r1_orders_2(A_19,C_27,'#skF_3'(A_19,B_26,C_27))
      | r1_lattice3(A_19,B_26,C_27)
      | ~ m1_subset_1(C_27,u1_struct_0(A_19))
      | ~ l1_orders_2(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_10026,plain,(
    ! [A_1332,B_26,B_1333] :
      ( r1_lattice3(k2_yellow_1(A_1332),B_26,B_1333)
      | ~ m1_subset_1(B_1333,u1_struct_0(k2_yellow_1(A_1332)))
      | ~ l1_orders_2(k2_yellow_1(A_1332))
      | v2_struct_0(k2_yellow_1(A_1332))
      | ~ r1_tarski(B_1333,'#skF_3'(k2_yellow_1(A_1332),B_26,B_1333))
      | ~ m1_subset_1('#skF_3'(k2_yellow_1(A_1332),B_26,B_1333),A_1332)
      | ~ m1_subset_1(B_1333,A_1332)
      | v1_xboole_0(A_1332) ) ),
    inference(resolution,[status(thm)],[c_10022,c_32])).

tff(c_22767,plain,(
    ! [A_1888,B_1889,B_1890] :
      ( r1_lattice3(k2_yellow_1(A_1888),B_1889,B_1890)
      | v2_struct_0(k2_yellow_1(A_1888))
      | ~ r1_tarski(B_1890,'#skF_3'(k2_yellow_1(A_1888),B_1889,B_1890))
      | ~ m1_subset_1('#skF_3'(k2_yellow_1(A_1888),B_1889,B_1890),A_1888)
      | ~ m1_subset_1(B_1890,A_1888)
      | v1_xboole_0(A_1888) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_64,c_10026])).

tff(c_22870,plain,(
    ! [A_1891,B_1892] :
      ( r1_lattice3(k2_yellow_1(A_1891),B_1892,k1_xboole_0)
      | v2_struct_0(k2_yellow_1(A_1891))
      | ~ m1_subset_1('#skF_3'(k2_yellow_1(A_1891),B_1892,k1_xboole_0),A_1891)
      | ~ m1_subset_1(k1_xboole_0,A_1891)
      | v1_xboole_0(A_1891) ) ),
    inference(resolution,[status(thm)],[c_12,c_22767])).

tff(c_22891,plain,(
    ! [B_1134] :
      ( v2_struct_0(k2_yellow_1(B_1134))
      | ~ m1_subset_1(k1_xboole_0,B_1134)
      | v1_xboole_0(B_1134)
      | r1_lattice3(k2_yellow_1(B_1134),B_1134,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(B_1134)))
      | ~ l1_orders_2(k2_yellow_1(B_1134)) ) ),
    inference(resolution,[status(thm)],[c_8626,c_22870])).

tff(c_22908,plain,(
    ! [B_1893] :
      ( v2_struct_0(k2_yellow_1(B_1893))
      | v1_xboole_0(B_1893)
      | r1_lattice3(k2_yellow_1(B_1893),B_1893,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,B_1893) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_64,c_22891])).

tff(c_8580,plain,(
    ! [A_1124,B_1125] :
      ( v1_yellow_0(A_1124)
      | ~ r1_lattice3(A_1124,u1_struct_0(A_1124),B_1125)
      | ~ m1_subset_1(B_1125,u1_struct_0(A_1124))
      | ~ l1_orders_2(A_1124) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_8586,plain,(
    ! [A_42,B_1125] :
      ( v1_yellow_0(k2_yellow_1(A_42))
      | ~ r1_lattice3(k2_yellow_1(A_42),A_42,B_1125)
      | ~ m1_subset_1(B_1125,u1_struct_0(k2_yellow_1(A_42)))
      | ~ l1_orders_2(k2_yellow_1(A_42)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_8580])).

tff(c_8589,plain,(
    ! [A_42,B_1125] :
      ( v1_yellow_0(k2_yellow_1(A_42))
      | ~ r1_lattice3(k2_yellow_1(A_42),A_42,B_1125)
      | ~ m1_subset_1(B_1125,A_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_64,c_8586])).

tff(c_22962,plain,(
    ! [B_1894] :
      ( v1_yellow_0(k2_yellow_1(B_1894))
      | v2_struct_0(k2_yellow_1(B_1894))
      | v1_xboole_0(B_1894)
      | ~ m1_subset_1(k1_xboole_0,B_1894) ) ),
    inference(resolution,[status(thm)],[c_22908,c_8589])).

tff(c_62,plain,(
    ! [A_41] :
      ( ~ v2_struct_0(k2_yellow_1(A_41))
      | v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_22973,plain,(
    ! [B_1896] :
      ( v1_yellow_0(k2_yellow_1(B_1896))
      | v1_xboole_0(B_1896)
      | ~ m1_subset_1(k1_xboole_0,B_1896) ) ),
    inference(resolution,[status(thm)],[c_22962,c_62])).

tff(c_383,plain,(
    ! [A_118,B_119,C_120] :
      ( r2_hidden('#skF_3'(A_118,B_119,C_120),B_119)
      | r1_lattice3(A_118,B_119,C_120)
      | ~ m1_subset_1(C_120,u1_struct_0(A_118))
      | ~ l1_orders_2(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_390,plain,(
    ! [A_118,B_119,C_120] :
      ( m1_subset_1('#skF_3'(A_118,B_119,C_120),B_119)
      | r1_lattice3(A_118,B_119,C_120)
      | ~ m1_subset_1(C_120,u1_struct_0(A_118))
      | ~ l1_orders_2(A_118) ) ),
    inference(resolution,[status(thm)],[c_383,c_24])).

tff(c_142,plain,(
    ! [A_68] :
      ( m1_subset_1(k3_yellow_0(A_68),u1_struct_0(A_68))
      | ~ l1_orders_2(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_148,plain,(
    ! [A_42] :
      ( m1_subset_1(k3_yellow_0(k2_yellow_1(A_42)),A_42)
      | ~ l1_orders_2(k2_yellow_1(A_42)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_142])).

tff(c_152,plain,(
    ! [A_69] : m1_subset_1(k3_yellow_0(k2_yellow_1(A_69)),A_69) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_148])).

tff(c_22,plain,(
    ! [B_13,A_12] :
      ( v1_xboole_0(B_13)
      | ~ m1_subset_1(B_13,A_12)
      | ~ v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_156,plain,(
    ! [A_69] :
      ( v1_xboole_0(k3_yellow_0(k2_yellow_1(A_69)))
      | ~ v1_xboole_0(A_69) ) ),
    inference(resolution,[status(thm)],[c_152,c_22])).

tff(c_172,plain,(
    ! [A_75,B_76] :
      ( r2_hidden('#skF_2'(A_75,B_76),A_75)
      | r1_tarski(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_199,plain,(
    ! [A_80,B_81] :
      ( ~ v1_xboole_0(A_80)
      | r1_tarski(A_80,B_81) ) ),
    inference(resolution,[status(thm)],[c_172,c_2])).

tff(c_14,plain,(
    ! [A_11] :
      ( k1_xboole_0 = A_11
      | ~ r1_tarski(A_11,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_205,plain,(
    ! [A_82] :
      ( k1_xboole_0 = A_82
      | ~ v1_xboole_0(A_82) ) ),
    inference(resolution,[status(thm)],[c_199,c_14])).

tff(c_258,plain,(
    ! [A_89] :
      ( k3_yellow_0(k2_yellow_1(A_89)) = k1_xboole_0
      | ~ v1_xboole_0(A_89) ) ),
    inference(resolution,[status(thm)],[c_156,c_205])).

tff(c_151,plain,(
    ! [A_42] : m1_subset_1(k3_yellow_0(k2_yellow_1(A_42)),A_42) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_148])).

tff(c_282,plain,(
    ! [A_90] :
      ( m1_subset_1(k1_xboole_0,A_90)
      | ~ v1_xboole_0(A_90) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_151])).

tff(c_286,plain,(
    ! [A_90] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(A_90) ) ),
    inference(resolution,[status(thm)],[c_282,c_22])).

tff(c_297,plain,(
    ! [A_90] : ~ v1_xboole_0(A_90) ),
    inference(splitLeft,[status(thm)],[c_286])).

tff(c_303,plain,(
    ! [A_41] : ~ v2_struct_0(k2_yellow_1(A_41)) ),
    inference(negUnitSimplification,[status(thm)],[c_297,c_62])).

tff(c_443,plain,(
    ! [A_43,B_47,C_49] :
      ( r3_orders_2(k2_yellow_1(A_43),B_47,C_49)
      | ~ r1_tarski(B_47,C_49)
      | ~ m1_subset_1(C_49,A_43)
      | ~ m1_subset_1(B_47,A_43) ) ),
    inference(negUnitSimplification,[status(thm)],[c_297,c_78])).

tff(c_639,plain,(
    ! [A_197,B_198,C_199] :
      ( r1_orders_2(A_197,B_198,C_199)
      | ~ r3_orders_2(A_197,B_198,C_199)
      | ~ m1_subset_1(C_199,u1_struct_0(A_197))
      | ~ m1_subset_1(B_198,u1_struct_0(A_197))
      | ~ l1_orders_2(A_197)
      | ~ v3_orders_2(A_197)
      | v2_struct_0(A_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_641,plain,(
    ! [A_43,B_47,C_49] :
      ( r1_orders_2(k2_yellow_1(A_43),B_47,C_49)
      | ~ m1_subset_1(C_49,u1_struct_0(k2_yellow_1(A_43)))
      | ~ m1_subset_1(B_47,u1_struct_0(k2_yellow_1(A_43)))
      | ~ l1_orders_2(k2_yellow_1(A_43))
      | ~ v3_orders_2(k2_yellow_1(A_43))
      | v2_struct_0(k2_yellow_1(A_43))
      | ~ r1_tarski(B_47,C_49)
      | ~ m1_subset_1(C_49,A_43)
      | ~ m1_subset_1(B_47,A_43) ) ),
    inference(resolution,[status(thm)],[c_443,c_639])).

tff(c_644,plain,(
    ! [A_43,B_47,C_49] :
      ( r1_orders_2(k2_yellow_1(A_43),B_47,C_49)
      | v2_struct_0(k2_yellow_1(A_43))
      | ~ r1_tarski(B_47,C_49)
      | ~ m1_subset_1(C_49,A_43)
      | ~ m1_subset_1(B_47,A_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_64,c_64,c_641])).

tff(c_646,plain,(
    ! [A_200,B_201,C_202] :
      ( r1_orders_2(k2_yellow_1(A_200),B_201,C_202)
      | ~ r1_tarski(B_201,C_202)
      | ~ m1_subset_1(C_202,A_200)
      | ~ m1_subset_1(B_201,A_200) ) ),
    inference(negUnitSimplification,[status(thm)],[c_303,c_644])).

tff(c_650,plain,(
    ! [A_200,B_26,B_201] :
      ( r1_lattice3(k2_yellow_1(A_200),B_26,B_201)
      | ~ m1_subset_1(B_201,u1_struct_0(k2_yellow_1(A_200)))
      | ~ l1_orders_2(k2_yellow_1(A_200))
      | ~ r1_tarski(B_201,'#skF_3'(k2_yellow_1(A_200),B_26,B_201))
      | ~ m1_subset_1('#skF_3'(k2_yellow_1(A_200),B_26,B_201),A_200)
      | ~ m1_subset_1(B_201,A_200) ) ),
    inference(resolution,[status(thm)],[c_646,c_32])).

tff(c_8227,plain,(
    ! [A_1097,B_1098,B_1099] :
      ( r1_lattice3(k2_yellow_1(A_1097),B_1098,B_1099)
      | ~ r1_tarski(B_1099,'#skF_3'(k2_yellow_1(A_1097),B_1098,B_1099))
      | ~ m1_subset_1('#skF_3'(k2_yellow_1(A_1097),B_1098,B_1099),A_1097)
      | ~ m1_subset_1(B_1099,A_1097) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_64,c_650])).

tff(c_8372,plain,(
    ! [A_1109,B_1110] :
      ( r1_lattice3(k2_yellow_1(A_1109),B_1110,k1_xboole_0)
      | ~ m1_subset_1('#skF_3'(k2_yellow_1(A_1109),B_1110,k1_xboole_0),A_1109)
      | ~ m1_subset_1(k1_xboole_0,A_1109) ) ),
    inference(resolution,[status(thm)],[c_12,c_8227])).

tff(c_8388,plain,(
    ! [B_119] :
      ( ~ m1_subset_1(k1_xboole_0,B_119)
      | r1_lattice3(k2_yellow_1(B_119),B_119,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(B_119)))
      | ~ l1_orders_2(k2_yellow_1(B_119)) ) ),
    inference(resolution,[status(thm)],[c_390,c_8372])).

tff(c_8411,plain,(
    ! [B_1111] :
      ( r1_lattice3(k2_yellow_1(B_1111),B_1111,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,B_1111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_64,c_8388])).

tff(c_344,plain,(
    ! [A_101,B_102] :
      ( v1_yellow_0(A_101)
      | ~ r1_lattice3(A_101,u1_struct_0(A_101),B_102)
      | ~ m1_subset_1(B_102,u1_struct_0(A_101))
      | ~ l1_orders_2(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_350,plain,(
    ! [A_42,B_102] :
      ( v1_yellow_0(k2_yellow_1(A_42))
      | ~ r1_lattice3(k2_yellow_1(A_42),A_42,B_102)
      | ~ m1_subset_1(B_102,u1_struct_0(k2_yellow_1(A_42)))
      | ~ l1_orders_2(k2_yellow_1(A_42)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_344])).

tff(c_353,plain,(
    ! [A_42,B_102] :
      ( v1_yellow_0(k2_yellow_1(A_42))
      | ~ r1_lattice3(k2_yellow_1(A_42),A_42,B_102)
      | ~ m1_subset_1(B_102,A_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_64,c_350])).

tff(c_8486,plain,(
    ! [B_1114] :
      ( v1_yellow_0(k2_yellow_1(B_1114))
      | ~ m1_subset_1(k1_xboole_0,B_1114) ) ),
    inference(resolution,[status(thm)],[c_8411,c_353])).

tff(c_336,plain,(
    ! [A_100] :
      ( r1_lattice3(A_100,u1_struct_0(A_100),'#skF_4'(A_100))
      | ~ v1_yellow_0(A_100)
      | ~ l1_orders_2(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_339,plain,(
    ! [A_42] :
      ( r1_lattice3(k2_yellow_1(A_42),A_42,'#skF_4'(k2_yellow_1(A_42)))
      | ~ v1_yellow_0(k2_yellow_1(A_42))
      | ~ l1_orders_2(k2_yellow_1(A_42)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_336])).

tff(c_341,plain,(
    ! [A_42] :
      ( r1_lattice3(k2_yellow_1(A_42),A_42,'#skF_4'(k2_yellow_1(A_42)))
      | ~ v1_yellow_0(k2_yellow_1(A_42)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_339])).

tff(c_545,plain,(
    ! [A_165,C_166,D_167,B_168] :
      ( r1_orders_2(A_165,C_166,D_167)
      | ~ r2_hidden(D_167,B_168)
      | ~ m1_subset_1(D_167,u1_struct_0(A_165))
      | ~ r1_lattice3(A_165,B_168,C_166)
      | ~ m1_subset_1(C_166,u1_struct_0(A_165))
      | ~ l1_orders_2(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_591,plain,(
    ! [A_178,C_179] :
      ( r1_orders_2(A_178,C_179,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,u1_struct_0(A_178))
      | ~ r1_lattice3(A_178,'#skF_5',C_179)
      | ~ m1_subset_1(C_179,u1_struct_0(A_178))
      | ~ l1_orders_2(A_178) ) ),
    inference(resolution,[status(thm)],[c_74,c_545])).

tff(c_593,plain,(
    ! [A_42,C_179] :
      ( r1_orders_2(k2_yellow_1(A_42),C_179,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,A_42)
      | ~ r1_lattice3(k2_yellow_1(A_42),'#skF_5',C_179)
      | ~ m1_subset_1(C_179,u1_struct_0(k2_yellow_1(A_42)))
      | ~ l1_orders_2(k2_yellow_1(A_42)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_591])).

tff(c_595,plain,(
    ! [A_42,C_179] :
      ( r1_orders_2(k2_yellow_1(A_42),C_179,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,A_42)
      | ~ r1_lattice3(k2_yellow_1(A_42),'#skF_5',C_179)
      | ~ m1_subset_1(C_179,A_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_64,c_593])).

tff(c_680,plain,(
    ! [A_224,B_225,C_226] :
      ( r3_orders_2(A_224,B_225,C_226)
      | ~ r1_orders_2(A_224,B_225,C_226)
      | ~ m1_subset_1(C_226,u1_struct_0(A_224))
      | ~ m1_subset_1(B_225,u1_struct_0(A_224))
      | ~ l1_orders_2(A_224)
      | ~ v3_orders_2(A_224)
      | v2_struct_0(A_224) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_733,plain,(
    ! [A_42,B_225,C_226] :
      ( r3_orders_2(k2_yellow_1(A_42),B_225,C_226)
      | ~ r1_orders_2(k2_yellow_1(A_42),B_225,C_226)
      | ~ m1_subset_1(C_226,A_42)
      | ~ m1_subset_1(B_225,u1_struct_0(k2_yellow_1(A_42)))
      | ~ l1_orders_2(k2_yellow_1(A_42))
      | ~ v3_orders_2(k2_yellow_1(A_42))
      | v2_struct_0(k2_yellow_1(A_42)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_680])).

tff(c_753,plain,(
    ! [A_42,B_225,C_226] :
      ( r3_orders_2(k2_yellow_1(A_42),B_225,C_226)
      | ~ r1_orders_2(k2_yellow_1(A_42),B_225,C_226)
      | ~ m1_subset_1(C_226,A_42)
      | ~ m1_subset_1(B_225,A_42)
      | v2_struct_0(k2_yellow_1(A_42)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_64,c_733])).

tff(c_755,plain,(
    ! [A_227,B_228,C_229] :
      ( r3_orders_2(k2_yellow_1(A_227),B_228,C_229)
      | ~ r1_orders_2(k2_yellow_1(A_227),B_228,C_229)
      | ~ m1_subset_1(C_229,A_227)
      | ~ m1_subset_1(B_228,A_227) ) ),
    inference(negUnitSimplification,[status(thm)],[c_303,c_753])).

tff(c_70,plain,(
    ! [B_47,C_49,A_43] :
      ( r1_tarski(B_47,C_49)
      | ~ r3_orders_2(k2_yellow_1(A_43),B_47,C_49)
      | ~ m1_subset_1(C_49,u1_struct_0(k2_yellow_1(A_43)))
      | ~ m1_subset_1(B_47,u1_struct_0(k2_yellow_1(A_43)))
      | v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_77,plain,(
    ! [B_47,C_49,A_43] :
      ( r1_tarski(B_47,C_49)
      | ~ r3_orders_2(k2_yellow_1(A_43),B_47,C_49)
      | ~ m1_subset_1(C_49,A_43)
      | ~ m1_subset_1(B_47,A_43)
      | v1_xboole_0(A_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_64,c_70])).

tff(c_366,plain,(
    ! [B_47,C_49,A_43] :
      ( r1_tarski(B_47,C_49)
      | ~ r3_orders_2(k2_yellow_1(A_43),B_47,C_49)
      | ~ m1_subset_1(C_49,A_43)
      | ~ m1_subset_1(B_47,A_43) ) ),
    inference(negUnitSimplification,[status(thm)],[c_297,c_77])).

tff(c_766,plain,(
    ! [B_230,C_231,A_232] :
      ( r1_tarski(B_230,C_231)
      | ~ r1_orders_2(k2_yellow_1(A_232),B_230,C_231)
      | ~ m1_subset_1(C_231,A_232)
      | ~ m1_subset_1(B_230,A_232) ) ),
    inference(resolution,[status(thm)],[c_755,c_366])).

tff(c_890,plain,(
    ! [C_246,A_247] :
      ( r1_tarski(C_246,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,A_247)
      | ~ r1_lattice3(k2_yellow_1(A_247),'#skF_5',C_246)
      | ~ m1_subset_1(C_246,A_247) ) ),
    inference(resolution,[status(thm)],[c_595,c_766])).

tff(c_894,plain,
    ( r1_tarski('#skF_4'(k2_yellow_1('#skF_5')),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,'#skF_5')
    | ~ m1_subset_1('#skF_4'(k2_yellow_1('#skF_5')),'#skF_5')
    | ~ v1_yellow_0(k2_yellow_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_341,c_890])).

tff(c_897,plain,
    ( r1_tarski('#skF_4'(k2_yellow_1('#skF_5')),k1_xboole_0)
    | ~ m1_subset_1('#skF_4'(k2_yellow_1('#skF_5')),'#skF_5')
    | ~ v1_yellow_0(k2_yellow_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_894])).

tff(c_898,plain,(
    ~ v1_yellow_0(k2_yellow_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_897])).

tff(c_8501,plain,(
    ~ m1_subset_1(k1_xboole_0,'#skF_5') ),
    inference(resolution,[status(thm)],[c_8486,c_898])).

tff(c_8513,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_8501])).

tff(c_8515,plain,(
    v1_yellow_0(k2_yellow_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_897])).

tff(c_58,plain,(
    ! [A_40] : v5_orders_2(k2_yellow_1(A_40)) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_46,plain,(
    ! [A_36,B_38] :
      ( r1_orders_2(A_36,k3_yellow_0(A_36),B_38)
      | ~ m1_subset_1(B_38,u1_struct_0(A_36))
      | ~ l1_orders_2(A_36)
      | ~ v1_yellow_0(A_36)
      | ~ v5_orders_2(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_798,plain,(
    ! [A_232,B_38] :
      ( r1_tarski(k3_yellow_0(k2_yellow_1(A_232)),B_38)
      | ~ m1_subset_1(B_38,A_232)
      | ~ m1_subset_1(k3_yellow_0(k2_yellow_1(A_232)),A_232)
      | ~ m1_subset_1(B_38,u1_struct_0(k2_yellow_1(A_232)))
      | ~ l1_orders_2(k2_yellow_1(A_232))
      | ~ v1_yellow_0(k2_yellow_1(A_232))
      | ~ v5_orders_2(k2_yellow_1(A_232))
      | v2_struct_0(k2_yellow_1(A_232)) ) ),
    inference(resolution,[status(thm)],[c_46,c_766])).

tff(c_819,plain,(
    ! [A_232,B_38] :
      ( r1_tarski(k3_yellow_0(k2_yellow_1(A_232)),B_38)
      | ~ m1_subset_1(B_38,A_232)
      | ~ v1_yellow_0(k2_yellow_1(A_232))
      | v2_struct_0(k2_yellow_1(A_232)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_50,c_64,c_151,c_798])).

tff(c_821,plain,(
    ! [A_233,B_234] :
      ( r1_tarski(k3_yellow_0(k2_yellow_1(A_233)),B_234)
      | ~ m1_subset_1(B_234,A_233)
      | ~ v1_yellow_0(k2_yellow_1(A_233)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_303,c_819])).

tff(c_842,plain,(
    ! [A_233] :
      ( k3_yellow_0(k2_yellow_1(A_233)) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,A_233)
      | ~ v1_yellow_0(k2_yellow_1(A_233)) ) ),
    inference(resolution,[status(thm)],[c_821,c_14])).

tff(c_8518,plain,
    ( k3_yellow_0(k2_yellow_1('#skF_5')) = k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,'#skF_5') ),
    inference(resolution,[status(thm)],[c_8515,c_842])).

tff(c_8521,plain,(
    k3_yellow_0(k2_yellow_1('#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_8518])).

tff(c_8523,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_8521])).

tff(c_8524,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_286])).

tff(c_9197,plain,(
    ! [A_1236,B_1237,C_1238] :
      ( r3_orders_2(A_1236,B_1237,C_1238)
      | ~ r1_orders_2(A_1236,B_1237,C_1238)
      | ~ m1_subset_1(C_1238,u1_struct_0(A_1236))
      | ~ m1_subset_1(B_1237,u1_struct_0(A_1236))
      | ~ l1_orders_2(A_1236)
      | ~ v3_orders_2(A_1236)
      | v2_struct_0(A_1236) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_9232,plain,(
    ! [A_42,B_1237,C_1238] :
      ( r3_orders_2(k2_yellow_1(A_42),B_1237,C_1238)
      | ~ r1_orders_2(k2_yellow_1(A_42),B_1237,C_1238)
      | ~ m1_subset_1(C_1238,A_42)
      | ~ m1_subset_1(B_1237,u1_struct_0(k2_yellow_1(A_42)))
      | ~ l1_orders_2(k2_yellow_1(A_42))
      | ~ v3_orders_2(k2_yellow_1(A_42))
      | v2_struct_0(k2_yellow_1(A_42)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_9197])).

tff(c_9664,plain,(
    ! [A_1298,B_1299,C_1300] :
      ( r3_orders_2(k2_yellow_1(A_1298),B_1299,C_1300)
      | ~ r1_orders_2(k2_yellow_1(A_1298),B_1299,C_1300)
      | ~ m1_subset_1(C_1300,A_1298)
      | ~ m1_subset_1(B_1299,A_1298)
      | v2_struct_0(k2_yellow_1(A_1298)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_64,c_9232])).

tff(c_10977,plain,(
    ! [B_1405,C_1406,A_1407] :
      ( r1_tarski(B_1405,C_1406)
      | v1_xboole_0(A_1407)
      | ~ r1_orders_2(k2_yellow_1(A_1407),B_1405,C_1406)
      | ~ m1_subset_1(C_1406,A_1407)
      | ~ m1_subset_1(B_1405,A_1407)
      | v2_struct_0(k2_yellow_1(A_1407)) ) ),
    inference(resolution,[status(thm)],[c_9664,c_77])).

tff(c_11038,plain,(
    ! [A_1407,B_38] :
      ( r1_tarski(k3_yellow_0(k2_yellow_1(A_1407)),B_38)
      | v1_xboole_0(A_1407)
      | ~ m1_subset_1(B_38,A_1407)
      | ~ m1_subset_1(k3_yellow_0(k2_yellow_1(A_1407)),A_1407)
      | ~ m1_subset_1(B_38,u1_struct_0(k2_yellow_1(A_1407)))
      | ~ l1_orders_2(k2_yellow_1(A_1407))
      | ~ v1_yellow_0(k2_yellow_1(A_1407))
      | ~ v5_orders_2(k2_yellow_1(A_1407))
      | v2_struct_0(k2_yellow_1(A_1407)) ) ),
    inference(resolution,[status(thm)],[c_46,c_10977])).

tff(c_11081,plain,(
    ! [A_1408,B_1409] :
      ( r1_tarski(k3_yellow_0(k2_yellow_1(A_1408)),B_1409)
      | v1_xboole_0(A_1408)
      | ~ m1_subset_1(B_1409,A_1408)
      | ~ v1_yellow_0(k2_yellow_1(A_1408))
      | v2_struct_0(k2_yellow_1(A_1408)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_50,c_64,c_151,c_11038])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_210,plain,(
    ! [C_83,B_84,A_85] :
      ( r2_hidden(C_83,B_84)
      | ~ r2_hidden(C_83,A_85)
      | ~ r1_tarski(A_85,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8568,plain,(
    ! [A_1122,B_1123] :
      ( r2_hidden('#skF_1'(A_1122),B_1123)
      | ~ r1_tarski(A_1122,B_1123)
      | v1_xboole_0(A_1122) ) ),
    inference(resolution,[status(thm)],[c_4,c_210])).

tff(c_8579,plain,(
    ! [B_1123,A_1122] :
      ( ~ v1_xboole_0(B_1123)
      | ~ r1_tarski(A_1122,B_1123)
      | v1_xboole_0(A_1122) ) ),
    inference(resolution,[status(thm)],[c_8568,c_2])).

tff(c_11194,plain,(
    ! [B_1417,A_1418] :
      ( ~ v1_xboole_0(B_1417)
      | v1_xboole_0(k3_yellow_0(k2_yellow_1(A_1418)))
      | v1_xboole_0(A_1418)
      | ~ m1_subset_1(B_1417,A_1418)
      | ~ v1_yellow_0(k2_yellow_1(A_1418))
      | v2_struct_0(k2_yellow_1(A_1418)) ) ),
    inference(resolution,[status(thm)],[c_11081,c_8579])).

tff(c_11222,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k3_yellow_0(k2_yellow_1('#skF_5')))
    | v1_xboole_0('#skF_5')
    | ~ v1_yellow_0(k2_yellow_1('#skF_5'))
    | v2_struct_0(k2_yellow_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_131,c_11194])).

tff(c_11240,plain,
    ( v1_xboole_0(k3_yellow_0(k2_yellow_1('#skF_5')))
    | v1_xboole_0('#skF_5')
    | ~ v1_yellow_0(k2_yellow_1('#skF_5'))
    | v2_struct_0(k2_yellow_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8524,c_11222])).

tff(c_11241,plain,
    ( v1_xboole_0(k3_yellow_0(k2_yellow_1('#skF_5')))
    | ~ v1_yellow_0(k2_yellow_1('#skF_5'))
    | v2_struct_0(k2_yellow_1('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_11240])).

tff(c_11296,plain,(
    ~ v1_yellow_0(k2_yellow_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_11241])).

tff(c_22988,plain,
    ( v1_xboole_0('#skF_5')
    | ~ m1_subset_1(k1_xboole_0,'#skF_5') ),
    inference(resolution,[status(thm)],[c_22973,c_11296])).

tff(c_22998,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_22988])).

tff(c_23000,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_22998])).

tff(c_23002,plain,(
    v1_yellow_0(k2_yellow_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_11241])).

tff(c_11129,plain,(
    ! [A_1412] :
      ( k3_yellow_0(k2_yellow_1(A_1412)) = k1_xboole_0
      | v1_xboole_0(A_1412)
      | ~ m1_subset_1(k1_xboole_0,A_1412)
      | ~ v1_yellow_0(k2_yellow_1(A_1412))
      | v2_struct_0(k2_yellow_1(A_1412)) ) ),
    inference(resolution,[status(thm)],[c_11081,c_14])).

tff(c_11133,plain,(
    ! [A_1412] :
      ( k3_yellow_0(k2_yellow_1(A_1412)) = k1_xboole_0
      | v1_xboole_0(A_1412)
      | ~ m1_subset_1(k1_xboole_0,A_1412)
      | ~ v1_yellow_0(k2_yellow_1(A_1412)) ) ),
    inference(resolution,[status(thm)],[c_11129,c_62])).

tff(c_23005,plain,
    ( k3_yellow_0(k2_yellow_1('#skF_5')) = k1_xboole_0
    | v1_xboole_0('#skF_5')
    | ~ m1_subset_1(k1_xboole_0,'#skF_5') ),
    inference(resolution,[status(thm)],[c_23002,c_11133])).

tff(c_23008,plain,
    ( k3_yellow_0(k2_yellow_1('#skF_5')) = k1_xboole_0
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_23005])).

tff(c_23010,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_72,c_23008])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.34  % CPULimit   : 60
% 0.19/0.34  % DateTime   : Tue Dec  1 15:55:49 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.05/5.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.14/5.32  
% 12.14/5.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.14/5.32  %$ r3_orders_2 > r1_orders_2 > r1_lattice3 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k3_yellow_0 > k2_yellow_1 > k1_yellow_1 > k1_xboole_0 > #skF_4 > #skF_1 > #skF_5 > #skF_3 > #skF_2
% 12.14/5.32  
% 12.14/5.32  %Foreground sorts:
% 12.14/5.32  
% 12.14/5.32  
% 12.14/5.32  %Background operators:
% 12.14/5.32  
% 12.14/5.32  
% 12.14/5.32  %Foreground operators:
% 12.14/5.32  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 12.14/5.32  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 12.14/5.32  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 12.14/5.32  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 12.14/5.32  tff('#skF_4', type, '#skF_4': $i > $i).
% 12.14/5.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.14/5.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.14/5.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 12.14/5.32  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 12.14/5.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.14/5.32  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 12.14/5.32  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 12.14/5.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.14/5.32  tff('#skF_5', type, '#skF_5': $i).
% 12.14/5.32  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 12.14/5.32  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 12.14/5.32  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 12.14/5.32  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 12.14/5.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.14/5.32  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 12.14/5.32  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 12.14/5.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.14/5.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 12.14/5.32  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 12.14/5.32  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 12.14/5.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 12.14/5.32  tff(v1_yellow_0, type, v1_yellow_0: $i > $o).
% 12.14/5.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.14/5.32  
% 12.14/5.35  tff(f_162, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (r2_hidden(k1_xboole_0, A) => (k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_yellow_1)).
% 12.14/5.35  tff(f_61, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 12.14/5.35  tff(f_121, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 12.14/5.35  tff(f_141, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 12.14/5.35  tff(f_90, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, C, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_lattice3)).
% 12.14/5.35  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 12.14/5.35  tff(f_129, axiom, (![A]: (((v1_orders_2(k2_yellow_1(A)) & v3_orders_2(k2_yellow_1(A))) & v4_orders_2(k2_yellow_1(A))) & v5_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow_1)).
% 12.14/5.35  tff(f_154, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r3_orders_2(k2_yellow_1(A), B, C) <=> r1_tarski(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_yellow_1)).
% 12.14/5.35  tff(f_76, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 12.14/5.35  tff(f_99, axiom, (![A]: (l1_orders_2(A) => (v1_yellow_0(A) <=> (?[B]: (m1_subset_1(B, u1_struct_0(A)) & r1_lattice3(A, u1_struct_0(A), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_yellow_0)).
% 12.14/5.35  tff(f_137, axiom, (![A]: (~v1_xboole_0(A) => (~v2_struct_0(k2_yellow_1(A)) & v1_orders_2(k2_yellow_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_yellow_1)).
% 12.14/5.35  tff(f_103, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(k3_yellow_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_yellow_0)).
% 12.14/5.35  tff(f_57, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 12.14/5.35  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 12.14/5.35  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 12.14/5.35  tff(f_44, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 12.14/5.35  tff(f_117, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, k3_yellow_0(A), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_yellow_0)).
% 12.14/5.35  tff(c_76, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_162])).
% 12.14/5.35  tff(c_72, plain, (k3_yellow_0(k2_yellow_1('#skF_5'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_162])).
% 12.14/5.35  tff(c_74, plain, (r2_hidden(k1_xboole_0, '#skF_5')), inference(cnfTransformation, [status(thm)], [f_162])).
% 12.14/5.35  tff(c_123, plain, (![A_63, B_64]: (m1_subset_1(A_63, B_64) | ~r2_hidden(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_61])).
% 12.14/5.35  tff(c_131, plain, (m1_subset_1(k1_xboole_0, '#skF_5')), inference(resolution, [status(thm)], [c_74, c_123])).
% 12.14/5.35  tff(c_50, plain, (![A_39]: (l1_orders_2(k2_yellow_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_121])).
% 12.14/5.35  tff(c_64, plain, (![A_42]: (u1_struct_0(k2_yellow_1(A_42))=A_42)), inference(cnfTransformation, [status(thm)], [f_141])).
% 12.14/5.35  tff(c_8616, plain, (![A_1133, B_1134, C_1135]: (r2_hidden('#skF_3'(A_1133, B_1134, C_1135), B_1134) | r1_lattice3(A_1133, B_1134, C_1135) | ~m1_subset_1(C_1135, u1_struct_0(A_1133)) | ~l1_orders_2(A_1133))), inference(cnfTransformation, [status(thm)], [f_90])).
% 12.14/5.35  tff(c_24, plain, (![A_14, B_15]: (m1_subset_1(A_14, B_15) | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_61])).
% 12.14/5.35  tff(c_8626, plain, (![A_1133, B_1134, C_1135]: (m1_subset_1('#skF_3'(A_1133, B_1134, C_1135), B_1134) | r1_lattice3(A_1133, B_1134, C_1135) | ~m1_subset_1(C_1135, u1_struct_0(A_1133)) | ~l1_orders_2(A_1133))), inference(resolution, [status(thm)], [c_8616, c_24])).
% 12.14/5.35  tff(c_12, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(cnfTransformation, [status(thm)], [f_40])).
% 12.14/5.35  tff(c_54, plain, (![A_40]: (v3_orders_2(k2_yellow_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_129])).
% 12.14/5.35  tff(c_68, plain, (![A_43, B_47, C_49]: (r3_orders_2(k2_yellow_1(A_43), B_47, C_49) | ~r1_tarski(B_47, C_49) | ~m1_subset_1(C_49, u1_struct_0(k2_yellow_1(A_43))) | ~m1_subset_1(B_47, u1_struct_0(k2_yellow_1(A_43))) | v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_154])).
% 12.14/5.35  tff(c_78, plain, (![A_43, B_47, C_49]: (r3_orders_2(k2_yellow_1(A_43), B_47, C_49) | ~r1_tarski(B_47, C_49) | ~m1_subset_1(C_49, A_43) | ~m1_subset_1(B_47, A_43) | v1_xboole_0(A_43))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_64, c_68])).
% 12.14/5.35  tff(c_9091, plain, (![A_1213, B_1214, C_1215]: (r1_orders_2(A_1213, B_1214, C_1215) | ~r3_orders_2(A_1213, B_1214, C_1215) | ~m1_subset_1(C_1215, u1_struct_0(A_1213)) | ~m1_subset_1(B_1214, u1_struct_0(A_1213)) | ~l1_orders_2(A_1213) | ~v3_orders_2(A_1213) | v2_struct_0(A_1213))), inference(cnfTransformation, [status(thm)], [f_76])).
% 12.14/5.35  tff(c_9093, plain, (![A_43, B_47, C_49]: (r1_orders_2(k2_yellow_1(A_43), B_47, C_49) | ~m1_subset_1(C_49, u1_struct_0(k2_yellow_1(A_43))) | ~m1_subset_1(B_47, u1_struct_0(k2_yellow_1(A_43))) | ~l1_orders_2(k2_yellow_1(A_43)) | ~v3_orders_2(k2_yellow_1(A_43)) | v2_struct_0(k2_yellow_1(A_43)) | ~r1_tarski(B_47, C_49) | ~m1_subset_1(C_49, A_43) | ~m1_subset_1(B_47, A_43) | v1_xboole_0(A_43))), inference(resolution, [status(thm)], [c_78, c_9091])).
% 12.14/5.35  tff(c_10022, plain, (![A_1332, B_1333, C_1334]: (r1_orders_2(k2_yellow_1(A_1332), B_1333, C_1334) | v2_struct_0(k2_yellow_1(A_1332)) | ~r1_tarski(B_1333, C_1334) | ~m1_subset_1(C_1334, A_1332) | ~m1_subset_1(B_1333, A_1332) | v1_xboole_0(A_1332))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_64, c_64, c_9093])).
% 12.14/5.35  tff(c_32, plain, (![A_19, C_27, B_26]: (~r1_orders_2(A_19, C_27, '#skF_3'(A_19, B_26, C_27)) | r1_lattice3(A_19, B_26, C_27) | ~m1_subset_1(C_27, u1_struct_0(A_19)) | ~l1_orders_2(A_19))), inference(cnfTransformation, [status(thm)], [f_90])).
% 12.14/5.35  tff(c_10026, plain, (![A_1332, B_26, B_1333]: (r1_lattice3(k2_yellow_1(A_1332), B_26, B_1333) | ~m1_subset_1(B_1333, u1_struct_0(k2_yellow_1(A_1332))) | ~l1_orders_2(k2_yellow_1(A_1332)) | v2_struct_0(k2_yellow_1(A_1332)) | ~r1_tarski(B_1333, '#skF_3'(k2_yellow_1(A_1332), B_26, B_1333)) | ~m1_subset_1('#skF_3'(k2_yellow_1(A_1332), B_26, B_1333), A_1332) | ~m1_subset_1(B_1333, A_1332) | v1_xboole_0(A_1332))), inference(resolution, [status(thm)], [c_10022, c_32])).
% 12.14/5.35  tff(c_22767, plain, (![A_1888, B_1889, B_1890]: (r1_lattice3(k2_yellow_1(A_1888), B_1889, B_1890) | v2_struct_0(k2_yellow_1(A_1888)) | ~r1_tarski(B_1890, '#skF_3'(k2_yellow_1(A_1888), B_1889, B_1890)) | ~m1_subset_1('#skF_3'(k2_yellow_1(A_1888), B_1889, B_1890), A_1888) | ~m1_subset_1(B_1890, A_1888) | v1_xboole_0(A_1888))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_64, c_10026])).
% 12.14/5.35  tff(c_22870, plain, (![A_1891, B_1892]: (r1_lattice3(k2_yellow_1(A_1891), B_1892, k1_xboole_0) | v2_struct_0(k2_yellow_1(A_1891)) | ~m1_subset_1('#skF_3'(k2_yellow_1(A_1891), B_1892, k1_xboole_0), A_1891) | ~m1_subset_1(k1_xboole_0, A_1891) | v1_xboole_0(A_1891))), inference(resolution, [status(thm)], [c_12, c_22767])).
% 12.14/5.35  tff(c_22891, plain, (![B_1134]: (v2_struct_0(k2_yellow_1(B_1134)) | ~m1_subset_1(k1_xboole_0, B_1134) | v1_xboole_0(B_1134) | r1_lattice3(k2_yellow_1(B_1134), B_1134, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, u1_struct_0(k2_yellow_1(B_1134))) | ~l1_orders_2(k2_yellow_1(B_1134)))), inference(resolution, [status(thm)], [c_8626, c_22870])).
% 12.14/5.35  tff(c_22908, plain, (![B_1893]: (v2_struct_0(k2_yellow_1(B_1893)) | v1_xboole_0(B_1893) | r1_lattice3(k2_yellow_1(B_1893), B_1893, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, B_1893))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_64, c_22891])).
% 12.14/5.35  tff(c_8580, plain, (![A_1124, B_1125]: (v1_yellow_0(A_1124) | ~r1_lattice3(A_1124, u1_struct_0(A_1124), B_1125) | ~m1_subset_1(B_1125, u1_struct_0(A_1124)) | ~l1_orders_2(A_1124))), inference(cnfTransformation, [status(thm)], [f_99])).
% 12.14/5.35  tff(c_8586, plain, (![A_42, B_1125]: (v1_yellow_0(k2_yellow_1(A_42)) | ~r1_lattice3(k2_yellow_1(A_42), A_42, B_1125) | ~m1_subset_1(B_1125, u1_struct_0(k2_yellow_1(A_42))) | ~l1_orders_2(k2_yellow_1(A_42)))), inference(superposition, [status(thm), theory('equality')], [c_64, c_8580])).
% 12.14/5.35  tff(c_8589, plain, (![A_42, B_1125]: (v1_yellow_0(k2_yellow_1(A_42)) | ~r1_lattice3(k2_yellow_1(A_42), A_42, B_1125) | ~m1_subset_1(B_1125, A_42))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_64, c_8586])).
% 12.14/5.35  tff(c_22962, plain, (![B_1894]: (v1_yellow_0(k2_yellow_1(B_1894)) | v2_struct_0(k2_yellow_1(B_1894)) | v1_xboole_0(B_1894) | ~m1_subset_1(k1_xboole_0, B_1894))), inference(resolution, [status(thm)], [c_22908, c_8589])).
% 12.14/5.35  tff(c_62, plain, (![A_41]: (~v2_struct_0(k2_yellow_1(A_41)) | v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_137])).
% 12.14/5.35  tff(c_22973, plain, (![B_1896]: (v1_yellow_0(k2_yellow_1(B_1896)) | v1_xboole_0(B_1896) | ~m1_subset_1(k1_xboole_0, B_1896))), inference(resolution, [status(thm)], [c_22962, c_62])).
% 12.14/5.35  tff(c_383, plain, (![A_118, B_119, C_120]: (r2_hidden('#skF_3'(A_118, B_119, C_120), B_119) | r1_lattice3(A_118, B_119, C_120) | ~m1_subset_1(C_120, u1_struct_0(A_118)) | ~l1_orders_2(A_118))), inference(cnfTransformation, [status(thm)], [f_90])).
% 12.14/5.35  tff(c_390, plain, (![A_118, B_119, C_120]: (m1_subset_1('#skF_3'(A_118, B_119, C_120), B_119) | r1_lattice3(A_118, B_119, C_120) | ~m1_subset_1(C_120, u1_struct_0(A_118)) | ~l1_orders_2(A_118))), inference(resolution, [status(thm)], [c_383, c_24])).
% 12.14/5.35  tff(c_142, plain, (![A_68]: (m1_subset_1(k3_yellow_0(A_68), u1_struct_0(A_68)) | ~l1_orders_2(A_68))), inference(cnfTransformation, [status(thm)], [f_103])).
% 12.14/5.35  tff(c_148, plain, (![A_42]: (m1_subset_1(k3_yellow_0(k2_yellow_1(A_42)), A_42) | ~l1_orders_2(k2_yellow_1(A_42)))), inference(superposition, [status(thm), theory('equality')], [c_64, c_142])).
% 12.14/5.35  tff(c_152, plain, (![A_69]: (m1_subset_1(k3_yellow_0(k2_yellow_1(A_69)), A_69))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_148])).
% 12.14/5.35  tff(c_22, plain, (![B_13, A_12]: (v1_xboole_0(B_13) | ~m1_subset_1(B_13, A_12) | ~v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 12.14/5.35  tff(c_156, plain, (![A_69]: (v1_xboole_0(k3_yellow_0(k2_yellow_1(A_69))) | ~v1_xboole_0(A_69))), inference(resolution, [status(thm)], [c_152, c_22])).
% 12.14/5.35  tff(c_172, plain, (![A_75, B_76]: (r2_hidden('#skF_2'(A_75, B_76), A_75) | r1_tarski(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_38])).
% 12.14/5.35  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.14/5.35  tff(c_199, plain, (![A_80, B_81]: (~v1_xboole_0(A_80) | r1_tarski(A_80, B_81))), inference(resolution, [status(thm)], [c_172, c_2])).
% 12.14/5.35  tff(c_14, plain, (![A_11]: (k1_xboole_0=A_11 | ~r1_tarski(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_44])).
% 12.14/5.35  tff(c_205, plain, (![A_82]: (k1_xboole_0=A_82 | ~v1_xboole_0(A_82))), inference(resolution, [status(thm)], [c_199, c_14])).
% 12.14/5.35  tff(c_258, plain, (![A_89]: (k3_yellow_0(k2_yellow_1(A_89))=k1_xboole_0 | ~v1_xboole_0(A_89))), inference(resolution, [status(thm)], [c_156, c_205])).
% 12.14/5.35  tff(c_151, plain, (![A_42]: (m1_subset_1(k3_yellow_0(k2_yellow_1(A_42)), A_42))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_148])).
% 12.14/5.35  tff(c_282, plain, (![A_90]: (m1_subset_1(k1_xboole_0, A_90) | ~v1_xboole_0(A_90))), inference(superposition, [status(thm), theory('equality')], [c_258, c_151])).
% 12.14/5.35  tff(c_286, plain, (![A_90]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(A_90))), inference(resolution, [status(thm)], [c_282, c_22])).
% 12.14/5.35  tff(c_297, plain, (![A_90]: (~v1_xboole_0(A_90))), inference(splitLeft, [status(thm)], [c_286])).
% 12.14/5.35  tff(c_303, plain, (![A_41]: (~v2_struct_0(k2_yellow_1(A_41)))), inference(negUnitSimplification, [status(thm)], [c_297, c_62])).
% 12.14/5.35  tff(c_443, plain, (![A_43, B_47, C_49]: (r3_orders_2(k2_yellow_1(A_43), B_47, C_49) | ~r1_tarski(B_47, C_49) | ~m1_subset_1(C_49, A_43) | ~m1_subset_1(B_47, A_43))), inference(negUnitSimplification, [status(thm)], [c_297, c_78])).
% 12.14/5.35  tff(c_639, plain, (![A_197, B_198, C_199]: (r1_orders_2(A_197, B_198, C_199) | ~r3_orders_2(A_197, B_198, C_199) | ~m1_subset_1(C_199, u1_struct_0(A_197)) | ~m1_subset_1(B_198, u1_struct_0(A_197)) | ~l1_orders_2(A_197) | ~v3_orders_2(A_197) | v2_struct_0(A_197))), inference(cnfTransformation, [status(thm)], [f_76])).
% 12.14/5.35  tff(c_641, plain, (![A_43, B_47, C_49]: (r1_orders_2(k2_yellow_1(A_43), B_47, C_49) | ~m1_subset_1(C_49, u1_struct_0(k2_yellow_1(A_43))) | ~m1_subset_1(B_47, u1_struct_0(k2_yellow_1(A_43))) | ~l1_orders_2(k2_yellow_1(A_43)) | ~v3_orders_2(k2_yellow_1(A_43)) | v2_struct_0(k2_yellow_1(A_43)) | ~r1_tarski(B_47, C_49) | ~m1_subset_1(C_49, A_43) | ~m1_subset_1(B_47, A_43))), inference(resolution, [status(thm)], [c_443, c_639])).
% 12.14/5.35  tff(c_644, plain, (![A_43, B_47, C_49]: (r1_orders_2(k2_yellow_1(A_43), B_47, C_49) | v2_struct_0(k2_yellow_1(A_43)) | ~r1_tarski(B_47, C_49) | ~m1_subset_1(C_49, A_43) | ~m1_subset_1(B_47, A_43))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_64, c_64, c_641])).
% 12.14/5.35  tff(c_646, plain, (![A_200, B_201, C_202]: (r1_orders_2(k2_yellow_1(A_200), B_201, C_202) | ~r1_tarski(B_201, C_202) | ~m1_subset_1(C_202, A_200) | ~m1_subset_1(B_201, A_200))), inference(negUnitSimplification, [status(thm)], [c_303, c_644])).
% 12.14/5.35  tff(c_650, plain, (![A_200, B_26, B_201]: (r1_lattice3(k2_yellow_1(A_200), B_26, B_201) | ~m1_subset_1(B_201, u1_struct_0(k2_yellow_1(A_200))) | ~l1_orders_2(k2_yellow_1(A_200)) | ~r1_tarski(B_201, '#skF_3'(k2_yellow_1(A_200), B_26, B_201)) | ~m1_subset_1('#skF_3'(k2_yellow_1(A_200), B_26, B_201), A_200) | ~m1_subset_1(B_201, A_200))), inference(resolution, [status(thm)], [c_646, c_32])).
% 12.14/5.35  tff(c_8227, plain, (![A_1097, B_1098, B_1099]: (r1_lattice3(k2_yellow_1(A_1097), B_1098, B_1099) | ~r1_tarski(B_1099, '#skF_3'(k2_yellow_1(A_1097), B_1098, B_1099)) | ~m1_subset_1('#skF_3'(k2_yellow_1(A_1097), B_1098, B_1099), A_1097) | ~m1_subset_1(B_1099, A_1097))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_64, c_650])).
% 12.14/5.35  tff(c_8372, plain, (![A_1109, B_1110]: (r1_lattice3(k2_yellow_1(A_1109), B_1110, k1_xboole_0) | ~m1_subset_1('#skF_3'(k2_yellow_1(A_1109), B_1110, k1_xboole_0), A_1109) | ~m1_subset_1(k1_xboole_0, A_1109))), inference(resolution, [status(thm)], [c_12, c_8227])).
% 12.14/5.35  tff(c_8388, plain, (![B_119]: (~m1_subset_1(k1_xboole_0, B_119) | r1_lattice3(k2_yellow_1(B_119), B_119, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, u1_struct_0(k2_yellow_1(B_119))) | ~l1_orders_2(k2_yellow_1(B_119)))), inference(resolution, [status(thm)], [c_390, c_8372])).
% 12.14/5.35  tff(c_8411, plain, (![B_1111]: (r1_lattice3(k2_yellow_1(B_1111), B_1111, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, B_1111))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_64, c_8388])).
% 12.14/5.35  tff(c_344, plain, (![A_101, B_102]: (v1_yellow_0(A_101) | ~r1_lattice3(A_101, u1_struct_0(A_101), B_102) | ~m1_subset_1(B_102, u1_struct_0(A_101)) | ~l1_orders_2(A_101))), inference(cnfTransformation, [status(thm)], [f_99])).
% 12.14/5.35  tff(c_350, plain, (![A_42, B_102]: (v1_yellow_0(k2_yellow_1(A_42)) | ~r1_lattice3(k2_yellow_1(A_42), A_42, B_102) | ~m1_subset_1(B_102, u1_struct_0(k2_yellow_1(A_42))) | ~l1_orders_2(k2_yellow_1(A_42)))), inference(superposition, [status(thm), theory('equality')], [c_64, c_344])).
% 12.14/5.35  tff(c_353, plain, (![A_42, B_102]: (v1_yellow_0(k2_yellow_1(A_42)) | ~r1_lattice3(k2_yellow_1(A_42), A_42, B_102) | ~m1_subset_1(B_102, A_42))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_64, c_350])).
% 12.14/5.35  tff(c_8486, plain, (![B_1114]: (v1_yellow_0(k2_yellow_1(B_1114)) | ~m1_subset_1(k1_xboole_0, B_1114))), inference(resolution, [status(thm)], [c_8411, c_353])).
% 12.14/5.35  tff(c_336, plain, (![A_100]: (r1_lattice3(A_100, u1_struct_0(A_100), '#skF_4'(A_100)) | ~v1_yellow_0(A_100) | ~l1_orders_2(A_100))), inference(cnfTransformation, [status(thm)], [f_99])).
% 12.14/5.35  tff(c_339, plain, (![A_42]: (r1_lattice3(k2_yellow_1(A_42), A_42, '#skF_4'(k2_yellow_1(A_42))) | ~v1_yellow_0(k2_yellow_1(A_42)) | ~l1_orders_2(k2_yellow_1(A_42)))), inference(superposition, [status(thm), theory('equality')], [c_64, c_336])).
% 12.14/5.35  tff(c_341, plain, (![A_42]: (r1_lattice3(k2_yellow_1(A_42), A_42, '#skF_4'(k2_yellow_1(A_42))) | ~v1_yellow_0(k2_yellow_1(A_42)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_339])).
% 12.14/5.35  tff(c_545, plain, (![A_165, C_166, D_167, B_168]: (r1_orders_2(A_165, C_166, D_167) | ~r2_hidden(D_167, B_168) | ~m1_subset_1(D_167, u1_struct_0(A_165)) | ~r1_lattice3(A_165, B_168, C_166) | ~m1_subset_1(C_166, u1_struct_0(A_165)) | ~l1_orders_2(A_165))), inference(cnfTransformation, [status(thm)], [f_90])).
% 12.14/5.35  tff(c_591, plain, (![A_178, C_179]: (r1_orders_2(A_178, C_179, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, u1_struct_0(A_178)) | ~r1_lattice3(A_178, '#skF_5', C_179) | ~m1_subset_1(C_179, u1_struct_0(A_178)) | ~l1_orders_2(A_178))), inference(resolution, [status(thm)], [c_74, c_545])).
% 12.14/5.35  tff(c_593, plain, (![A_42, C_179]: (r1_orders_2(k2_yellow_1(A_42), C_179, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, A_42) | ~r1_lattice3(k2_yellow_1(A_42), '#skF_5', C_179) | ~m1_subset_1(C_179, u1_struct_0(k2_yellow_1(A_42))) | ~l1_orders_2(k2_yellow_1(A_42)))), inference(superposition, [status(thm), theory('equality')], [c_64, c_591])).
% 12.14/5.35  tff(c_595, plain, (![A_42, C_179]: (r1_orders_2(k2_yellow_1(A_42), C_179, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, A_42) | ~r1_lattice3(k2_yellow_1(A_42), '#skF_5', C_179) | ~m1_subset_1(C_179, A_42))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_64, c_593])).
% 12.14/5.35  tff(c_680, plain, (![A_224, B_225, C_226]: (r3_orders_2(A_224, B_225, C_226) | ~r1_orders_2(A_224, B_225, C_226) | ~m1_subset_1(C_226, u1_struct_0(A_224)) | ~m1_subset_1(B_225, u1_struct_0(A_224)) | ~l1_orders_2(A_224) | ~v3_orders_2(A_224) | v2_struct_0(A_224))), inference(cnfTransformation, [status(thm)], [f_76])).
% 12.14/5.35  tff(c_733, plain, (![A_42, B_225, C_226]: (r3_orders_2(k2_yellow_1(A_42), B_225, C_226) | ~r1_orders_2(k2_yellow_1(A_42), B_225, C_226) | ~m1_subset_1(C_226, A_42) | ~m1_subset_1(B_225, u1_struct_0(k2_yellow_1(A_42))) | ~l1_orders_2(k2_yellow_1(A_42)) | ~v3_orders_2(k2_yellow_1(A_42)) | v2_struct_0(k2_yellow_1(A_42)))), inference(superposition, [status(thm), theory('equality')], [c_64, c_680])).
% 12.14/5.35  tff(c_753, plain, (![A_42, B_225, C_226]: (r3_orders_2(k2_yellow_1(A_42), B_225, C_226) | ~r1_orders_2(k2_yellow_1(A_42), B_225, C_226) | ~m1_subset_1(C_226, A_42) | ~m1_subset_1(B_225, A_42) | v2_struct_0(k2_yellow_1(A_42)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_64, c_733])).
% 12.14/5.35  tff(c_755, plain, (![A_227, B_228, C_229]: (r3_orders_2(k2_yellow_1(A_227), B_228, C_229) | ~r1_orders_2(k2_yellow_1(A_227), B_228, C_229) | ~m1_subset_1(C_229, A_227) | ~m1_subset_1(B_228, A_227))), inference(negUnitSimplification, [status(thm)], [c_303, c_753])).
% 12.14/5.35  tff(c_70, plain, (![B_47, C_49, A_43]: (r1_tarski(B_47, C_49) | ~r3_orders_2(k2_yellow_1(A_43), B_47, C_49) | ~m1_subset_1(C_49, u1_struct_0(k2_yellow_1(A_43))) | ~m1_subset_1(B_47, u1_struct_0(k2_yellow_1(A_43))) | v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_154])).
% 12.14/5.35  tff(c_77, plain, (![B_47, C_49, A_43]: (r1_tarski(B_47, C_49) | ~r3_orders_2(k2_yellow_1(A_43), B_47, C_49) | ~m1_subset_1(C_49, A_43) | ~m1_subset_1(B_47, A_43) | v1_xboole_0(A_43))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_64, c_70])).
% 12.14/5.35  tff(c_366, plain, (![B_47, C_49, A_43]: (r1_tarski(B_47, C_49) | ~r3_orders_2(k2_yellow_1(A_43), B_47, C_49) | ~m1_subset_1(C_49, A_43) | ~m1_subset_1(B_47, A_43))), inference(negUnitSimplification, [status(thm)], [c_297, c_77])).
% 12.14/5.35  tff(c_766, plain, (![B_230, C_231, A_232]: (r1_tarski(B_230, C_231) | ~r1_orders_2(k2_yellow_1(A_232), B_230, C_231) | ~m1_subset_1(C_231, A_232) | ~m1_subset_1(B_230, A_232))), inference(resolution, [status(thm)], [c_755, c_366])).
% 12.14/5.35  tff(c_890, plain, (![C_246, A_247]: (r1_tarski(C_246, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, A_247) | ~r1_lattice3(k2_yellow_1(A_247), '#skF_5', C_246) | ~m1_subset_1(C_246, A_247))), inference(resolution, [status(thm)], [c_595, c_766])).
% 12.14/5.35  tff(c_894, plain, (r1_tarski('#skF_4'(k2_yellow_1('#skF_5')), k1_xboole_0) | ~m1_subset_1(k1_xboole_0, '#skF_5') | ~m1_subset_1('#skF_4'(k2_yellow_1('#skF_5')), '#skF_5') | ~v1_yellow_0(k2_yellow_1('#skF_5'))), inference(resolution, [status(thm)], [c_341, c_890])).
% 12.14/5.35  tff(c_897, plain, (r1_tarski('#skF_4'(k2_yellow_1('#skF_5')), k1_xboole_0) | ~m1_subset_1('#skF_4'(k2_yellow_1('#skF_5')), '#skF_5') | ~v1_yellow_0(k2_yellow_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_894])).
% 12.14/5.35  tff(c_898, plain, (~v1_yellow_0(k2_yellow_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_897])).
% 12.14/5.35  tff(c_8501, plain, (~m1_subset_1(k1_xboole_0, '#skF_5')), inference(resolution, [status(thm)], [c_8486, c_898])).
% 12.14/5.35  tff(c_8513, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_131, c_8501])).
% 12.14/5.35  tff(c_8515, plain, (v1_yellow_0(k2_yellow_1('#skF_5'))), inference(splitRight, [status(thm)], [c_897])).
% 12.14/5.35  tff(c_58, plain, (![A_40]: (v5_orders_2(k2_yellow_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_129])).
% 12.14/5.35  tff(c_46, plain, (![A_36, B_38]: (r1_orders_2(A_36, k3_yellow_0(A_36), B_38) | ~m1_subset_1(B_38, u1_struct_0(A_36)) | ~l1_orders_2(A_36) | ~v1_yellow_0(A_36) | ~v5_orders_2(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_117])).
% 12.14/5.35  tff(c_798, plain, (![A_232, B_38]: (r1_tarski(k3_yellow_0(k2_yellow_1(A_232)), B_38) | ~m1_subset_1(B_38, A_232) | ~m1_subset_1(k3_yellow_0(k2_yellow_1(A_232)), A_232) | ~m1_subset_1(B_38, u1_struct_0(k2_yellow_1(A_232))) | ~l1_orders_2(k2_yellow_1(A_232)) | ~v1_yellow_0(k2_yellow_1(A_232)) | ~v5_orders_2(k2_yellow_1(A_232)) | v2_struct_0(k2_yellow_1(A_232)))), inference(resolution, [status(thm)], [c_46, c_766])).
% 12.14/5.35  tff(c_819, plain, (![A_232, B_38]: (r1_tarski(k3_yellow_0(k2_yellow_1(A_232)), B_38) | ~m1_subset_1(B_38, A_232) | ~v1_yellow_0(k2_yellow_1(A_232)) | v2_struct_0(k2_yellow_1(A_232)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_50, c_64, c_151, c_798])).
% 12.14/5.35  tff(c_821, plain, (![A_233, B_234]: (r1_tarski(k3_yellow_0(k2_yellow_1(A_233)), B_234) | ~m1_subset_1(B_234, A_233) | ~v1_yellow_0(k2_yellow_1(A_233)))), inference(negUnitSimplification, [status(thm)], [c_303, c_819])).
% 12.14/5.35  tff(c_842, plain, (![A_233]: (k3_yellow_0(k2_yellow_1(A_233))=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, A_233) | ~v1_yellow_0(k2_yellow_1(A_233)))), inference(resolution, [status(thm)], [c_821, c_14])).
% 12.14/5.35  tff(c_8518, plain, (k3_yellow_0(k2_yellow_1('#skF_5'))=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, '#skF_5')), inference(resolution, [status(thm)], [c_8515, c_842])).
% 12.14/5.35  tff(c_8521, plain, (k3_yellow_0(k2_yellow_1('#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_131, c_8518])).
% 12.14/5.35  tff(c_8523, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_8521])).
% 12.14/5.35  tff(c_8524, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_286])).
% 12.14/5.35  tff(c_9197, plain, (![A_1236, B_1237, C_1238]: (r3_orders_2(A_1236, B_1237, C_1238) | ~r1_orders_2(A_1236, B_1237, C_1238) | ~m1_subset_1(C_1238, u1_struct_0(A_1236)) | ~m1_subset_1(B_1237, u1_struct_0(A_1236)) | ~l1_orders_2(A_1236) | ~v3_orders_2(A_1236) | v2_struct_0(A_1236))), inference(cnfTransformation, [status(thm)], [f_76])).
% 12.14/5.35  tff(c_9232, plain, (![A_42, B_1237, C_1238]: (r3_orders_2(k2_yellow_1(A_42), B_1237, C_1238) | ~r1_orders_2(k2_yellow_1(A_42), B_1237, C_1238) | ~m1_subset_1(C_1238, A_42) | ~m1_subset_1(B_1237, u1_struct_0(k2_yellow_1(A_42))) | ~l1_orders_2(k2_yellow_1(A_42)) | ~v3_orders_2(k2_yellow_1(A_42)) | v2_struct_0(k2_yellow_1(A_42)))), inference(superposition, [status(thm), theory('equality')], [c_64, c_9197])).
% 12.14/5.35  tff(c_9664, plain, (![A_1298, B_1299, C_1300]: (r3_orders_2(k2_yellow_1(A_1298), B_1299, C_1300) | ~r1_orders_2(k2_yellow_1(A_1298), B_1299, C_1300) | ~m1_subset_1(C_1300, A_1298) | ~m1_subset_1(B_1299, A_1298) | v2_struct_0(k2_yellow_1(A_1298)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_64, c_9232])).
% 12.14/5.35  tff(c_10977, plain, (![B_1405, C_1406, A_1407]: (r1_tarski(B_1405, C_1406) | v1_xboole_0(A_1407) | ~r1_orders_2(k2_yellow_1(A_1407), B_1405, C_1406) | ~m1_subset_1(C_1406, A_1407) | ~m1_subset_1(B_1405, A_1407) | v2_struct_0(k2_yellow_1(A_1407)))), inference(resolution, [status(thm)], [c_9664, c_77])).
% 12.14/5.35  tff(c_11038, plain, (![A_1407, B_38]: (r1_tarski(k3_yellow_0(k2_yellow_1(A_1407)), B_38) | v1_xboole_0(A_1407) | ~m1_subset_1(B_38, A_1407) | ~m1_subset_1(k3_yellow_0(k2_yellow_1(A_1407)), A_1407) | ~m1_subset_1(B_38, u1_struct_0(k2_yellow_1(A_1407))) | ~l1_orders_2(k2_yellow_1(A_1407)) | ~v1_yellow_0(k2_yellow_1(A_1407)) | ~v5_orders_2(k2_yellow_1(A_1407)) | v2_struct_0(k2_yellow_1(A_1407)))), inference(resolution, [status(thm)], [c_46, c_10977])).
% 12.14/5.35  tff(c_11081, plain, (![A_1408, B_1409]: (r1_tarski(k3_yellow_0(k2_yellow_1(A_1408)), B_1409) | v1_xboole_0(A_1408) | ~m1_subset_1(B_1409, A_1408) | ~v1_yellow_0(k2_yellow_1(A_1408)) | v2_struct_0(k2_yellow_1(A_1408)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_50, c_64, c_151, c_11038])).
% 12.14/5.35  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.14/5.35  tff(c_210, plain, (![C_83, B_84, A_85]: (r2_hidden(C_83, B_84) | ~r2_hidden(C_83, A_85) | ~r1_tarski(A_85, B_84))), inference(cnfTransformation, [status(thm)], [f_38])).
% 12.14/5.35  tff(c_8568, plain, (![A_1122, B_1123]: (r2_hidden('#skF_1'(A_1122), B_1123) | ~r1_tarski(A_1122, B_1123) | v1_xboole_0(A_1122))), inference(resolution, [status(thm)], [c_4, c_210])).
% 12.14/5.35  tff(c_8579, plain, (![B_1123, A_1122]: (~v1_xboole_0(B_1123) | ~r1_tarski(A_1122, B_1123) | v1_xboole_0(A_1122))), inference(resolution, [status(thm)], [c_8568, c_2])).
% 12.14/5.35  tff(c_11194, plain, (![B_1417, A_1418]: (~v1_xboole_0(B_1417) | v1_xboole_0(k3_yellow_0(k2_yellow_1(A_1418))) | v1_xboole_0(A_1418) | ~m1_subset_1(B_1417, A_1418) | ~v1_yellow_0(k2_yellow_1(A_1418)) | v2_struct_0(k2_yellow_1(A_1418)))), inference(resolution, [status(thm)], [c_11081, c_8579])).
% 12.14/5.35  tff(c_11222, plain, (~v1_xboole_0(k1_xboole_0) | v1_xboole_0(k3_yellow_0(k2_yellow_1('#skF_5'))) | v1_xboole_0('#skF_5') | ~v1_yellow_0(k2_yellow_1('#skF_5')) | v2_struct_0(k2_yellow_1('#skF_5'))), inference(resolution, [status(thm)], [c_131, c_11194])).
% 12.14/5.35  tff(c_11240, plain, (v1_xboole_0(k3_yellow_0(k2_yellow_1('#skF_5'))) | v1_xboole_0('#skF_5') | ~v1_yellow_0(k2_yellow_1('#skF_5')) | v2_struct_0(k2_yellow_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_8524, c_11222])).
% 12.14/5.35  tff(c_11241, plain, (v1_xboole_0(k3_yellow_0(k2_yellow_1('#skF_5'))) | ~v1_yellow_0(k2_yellow_1('#skF_5')) | v2_struct_0(k2_yellow_1('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_76, c_11240])).
% 12.14/5.35  tff(c_11296, plain, (~v1_yellow_0(k2_yellow_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_11241])).
% 12.14/5.35  tff(c_22988, plain, (v1_xboole_0('#skF_5') | ~m1_subset_1(k1_xboole_0, '#skF_5')), inference(resolution, [status(thm)], [c_22973, c_11296])).
% 12.14/5.35  tff(c_22998, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_131, c_22988])).
% 12.14/5.35  tff(c_23000, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_22998])).
% 12.14/5.35  tff(c_23002, plain, (v1_yellow_0(k2_yellow_1('#skF_5'))), inference(splitRight, [status(thm)], [c_11241])).
% 12.14/5.35  tff(c_11129, plain, (![A_1412]: (k3_yellow_0(k2_yellow_1(A_1412))=k1_xboole_0 | v1_xboole_0(A_1412) | ~m1_subset_1(k1_xboole_0, A_1412) | ~v1_yellow_0(k2_yellow_1(A_1412)) | v2_struct_0(k2_yellow_1(A_1412)))), inference(resolution, [status(thm)], [c_11081, c_14])).
% 12.14/5.35  tff(c_11133, plain, (![A_1412]: (k3_yellow_0(k2_yellow_1(A_1412))=k1_xboole_0 | v1_xboole_0(A_1412) | ~m1_subset_1(k1_xboole_0, A_1412) | ~v1_yellow_0(k2_yellow_1(A_1412)))), inference(resolution, [status(thm)], [c_11129, c_62])).
% 12.14/5.35  tff(c_23005, plain, (k3_yellow_0(k2_yellow_1('#skF_5'))=k1_xboole_0 | v1_xboole_0('#skF_5') | ~m1_subset_1(k1_xboole_0, '#skF_5')), inference(resolution, [status(thm)], [c_23002, c_11133])).
% 12.14/5.35  tff(c_23008, plain, (k3_yellow_0(k2_yellow_1('#skF_5'))=k1_xboole_0 | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_131, c_23005])).
% 12.14/5.35  tff(c_23010, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_72, c_23008])).
% 12.14/5.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.14/5.35  
% 12.14/5.35  Inference rules
% 12.14/5.35  ----------------------
% 12.14/5.35  #Ref     : 0
% 12.14/5.35  #Sup     : 4603
% 12.14/5.35  #Fact    : 24
% 12.14/5.35  #Define  : 0
% 12.14/5.35  #Split   : 41
% 12.14/5.35  #Chain   : 0
% 12.14/5.35  #Close   : 0
% 12.14/5.35  
% 12.14/5.35  Ordering : KBO
% 12.14/5.35  
% 12.14/5.35  Simplification rules
% 12.14/5.35  ----------------------
% 12.14/5.35  #Subsume      : 2569
% 12.14/5.35  #Demod        : 6249
% 12.14/5.35  #Tautology    : 927
% 12.14/5.35  #SimpNegUnit  : 333
% 12.14/5.35  #BackRed      : 85
% 12.14/5.35  
% 12.14/5.35  #Partial instantiations: 0
% 12.14/5.35  #Strategies tried      : 1
% 12.14/5.35  
% 12.14/5.35  Timing (in seconds)
% 12.14/5.35  ----------------------
% 12.14/5.35  Preprocessing        : 0.30
% 12.14/5.35  Parsing              : 0.16
% 12.14/5.35  CNF conversion       : 0.03
% 12.14/5.35  Main loop            : 4.15
% 12.14/5.35  Inferencing          : 1.31
% 12.14/5.35  Reduction            : 1.19
% 12.14/5.35  Demodulation         : 0.80
% 12.14/5.35  BG Simplification    : 0.08
% 12.14/5.35  Subsumption          : 1.34
% 12.14/5.35  Abstraction          : 0.13
% 12.14/5.35  MUC search           : 0.00
% 12.14/5.35  Cooper               : 0.00
% 12.14/5.35  Total                : 4.50
% 12.14/5.36  Index Insertion      : 0.00
% 12.14/5.36  Index Deletion       : 0.00
% 12.14/5.36  Index Matching       : 0.00
% 12.14/5.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
