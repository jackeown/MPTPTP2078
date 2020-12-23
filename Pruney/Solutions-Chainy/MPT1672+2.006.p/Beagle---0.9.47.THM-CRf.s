%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:01 EST 2020

% Result     : Theorem 7.93s
% Output     : CNFRefutation 8.27s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 238 expanded)
%              Number of leaves         :   41 ( 101 expanded)
%              Depth                    :   22
%              Number of atoms          :  449 (1577 expanded)
%              Number of equality atoms :   38 ( 166 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_finset_1 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_yellow_0,type,(
    k1_yellow_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(r1_yellow_0,type,(
    r1_yellow_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(v1_finset_1,type,(
    v1_finset_1: $i > $o )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_198,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( ! [D] :
                        ( ( v1_finset_1(D)
                          & m1_subset_1(D,k1_zfmisc_1(B)) )
                       => ( D != k1_xboole_0
                         => r1_yellow_0(A,D) ) )
                    & ! [D] :
                        ( m1_subset_1(D,u1_struct_0(A))
                       => ~ ( r2_hidden(D,C)
                            & ! [E] :
                                ( ( v1_finset_1(E)
                                  & m1_subset_1(E,k1_zfmisc_1(B)) )
                               => ~ ( r1_yellow_0(A,E)
                                    & D = k1_yellow_0(A,E) ) ) ) )
                    & ! [D] :
                        ( ( v1_finset_1(D)
                          & m1_subset_1(D,k1_zfmisc_1(B)) )
                       => ( D != k1_xboole_0
                         => r2_hidden(k1_yellow_0(A,D),C) ) ) )
                 => ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r2_lattice3(A,B,D)
                      <=> r2_lattice3(A,C,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_waybel_0)).

tff(f_81,axiom,(
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

tff(f_33,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_39,axiom,(
    ! [A] : v1_finset_1(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_finset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => r3_orders_2(A,B,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_123,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ( r1_lattice3(A,k1_tarski(C),B)
                 => r1_orders_2(A,B,C) )
                & ( r1_orders_2(A,B,C)
                 => r1_lattice3(A,k1_tarski(C),B) )
                & ( r2_lattice3(A,k1_tarski(C),B)
                 => r1_orders_2(A,C,B) )
                & ( r1_orders_2(A,C,B)
                 => r2_lattice3(A,k1_tarski(C),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_yellow_0)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r1_yellow_0(A,B)
           => ( C = k1_yellow_0(A,B)
            <=> ( r2_lattice3(A,B,C)
                & ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r2_lattice3(A,B,D)
                     => r1_orders_2(A,C,D) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_yellow_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_139,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => ! [D] :
              ( m1_subset_1(D,u1_struct_0(A))
             => ( ( r1_lattice3(A,C,D)
                 => r1_lattice3(A,B,D) )
                & ( r2_lattice3(A,C,D)
                 => r2_lattice3(A,B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_yellow_0)).

tff(f_29,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_74,plain,
    ( r2_lattice3('#skF_3','#skF_4','#skF_7')
    | r2_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_99,plain,(
    r2_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_68,plain,
    ( ~ r2_lattice3('#skF_3','#skF_5','#skF_7')
    | ~ r2_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_101,plain,(
    ~ r2_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_68])).

tff(c_60,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_50,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_24,plain,(
    ! [A_13,B_20,C_21] :
      ( r2_hidden('#skF_1'(A_13,B_20,C_21),B_20)
      | r2_lattice3(A_13,B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0(A_13))
      | ~ l1_orders_2(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1(k1_tarski(A_2),k1_zfmisc_1(B_3))
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_6] : v1_finset_1(k1_tarski(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_26,plain,(
    ! [A_13,B_20,C_21] :
      ( m1_subset_1('#skF_1'(A_13,B_20,C_21),u1_struct_0(A_13))
      | r2_lattice3(A_13,B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0(A_13))
      | ~ l1_orders_2(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_64,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_205,plain,(
    ! [A_146,B_147,C_148] :
      ( r3_orders_2(A_146,B_147,B_147)
      | ~ m1_subset_1(C_148,u1_struct_0(A_146))
      | ~ m1_subset_1(B_147,u1_struct_0(A_146))
      | ~ l1_orders_2(A_146)
      | ~ v3_orders_2(A_146)
      | v2_struct_0(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_209,plain,(
    ! [B_147] :
      ( r3_orders_2('#skF_3',B_147,B_147)
      | ~ m1_subset_1(B_147,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_205])).

tff(c_213,plain,(
    ! [B_147] :
      ( r3_orders_2('#skF_3',B_147,B_147)
      | ~ m1_subset_1(B_147,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_209])).

tff(c_215,plain,(
    ! [B_149] :
      ( r3_orders_2('#skF_3',B_149,B_149)
      | ~ m1_subset_1(B_149,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_213])).

tff(c_218,plain,(
    ! [B_20,C_21] :
      ( r3_orders_2('#skF_3','#skF_1'('#skF_3',B_20,C_21),'#skF_1'('#skF_3',B_20,C_21))
      | r2_lattice3('#skF_3',B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26,c_215])).

tff(c_223,plain,(
    ! [B_20,C_21] :
      ( r3_orders_2('#skF_3','#skF_1'('#skF_3',B_20,C_21),'#skF_1'('#skF_3',B_20,C_21))
      | r2_lattice3('#skF_3',B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_218])).

tff(c_329,plain,(
    ! [A_185,B_186,C_187] :
      ( r1_orders_2(A_185,B_186,C_187)
      | ~ r3_orders_2(A_185,B_186,C_187)
      | ~ m1_subset_1(C_187,u1_struct_0(A_185))
      | ~ m1_subset_1(B_186,u1_struct_0(A_185))
      | ~ l1_orders_2(A_185)
      | ~ v3_orders_2(A_185)
      | v2_struct_0(A_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_331,plain,(
    ! [B_20,C_21] :
      ( r1_orders_2('#skF_3','#skF_1'('#skF_3',B_20,C_21),'#skF_1'('#skF_3',B_20,C_21))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_20,C_21),u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3')
      | r2_lattice3('#skF_3',B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_223,c_329])).

tff(c_336,plain,(
    ! [B_20,C_21] :
      ( r1_orders_2('#skF_3','#skF_1'('#skF_3',B_20,C_21),'#skF_1'('#skF_3',B_20,C_21))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_20,C_21),u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3')
      | r2_lattice3('#skF_3',B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_331])).

tff(c_337,plain,(
    ! [B_20,C_21] :
      ( r1_orders_2('#skF_3','#skF_1'('#skF_3',B_20,C_21),'#skF_1'('#skF_3',B_20,C_21))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_20,C_21),u1_struct_0('#skF_3'))
      | r2_lattice3('#skF_3',B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_336])).

tff(c_115,plain,(
    ! [D_115] :
      ( r1_yellow_0('#skF_3',D_115)
      | k1_xboole_0 = D_115
      | ~ m1_subset_1(D_115,k1_zfmisc_1('#skF_4'))
      | ~ v1_finset_1(D_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_119,plain,(
    ! [A_2] :
      ( r1_yellow_0('#skF_3',k1_tarski(A_2))
      | k1_tarski(A_2) = k1_xboole_0
      | ~ v1_finset_1(k1_tarski(A_2))
      | ~ r2_hidden(A_2,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_6,c_115])).

tff(c_126,plain,(
    ! [A_2] :
      ( r1_yellow_0('#skF_3',k1_tarski(A_2))
      | k1_tarski(A_2) = k1_xboole_0
      | ~ r2_hidden(A_2,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_119])).

tff(c_38,plain,(
    ! [A_37,C_43,B_41] :
      ( r2_lattice3(A_37,k1_tarski(C_43),B_41)
      | ~ r1_orders_2(A_37,C_43,B_41)
      | ~ m1_subset_1(C_43,u1_struct_0(A_37))
      | ~ m1_subset_1(B_41,u1_struct_0(A_37))
      | ~ l1_orders_2(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_32,plain,(
    ! [A_25,B_32,C_33] :
      ( m1_subset_1('#skF_2'(A_25,B_32,C_33),u1_struct_0(A_25))
      | k1_yellow_0(A_25,B_32) = C_33
      | ~ r2_lattice3(A_25,B_32,C_33)
      | ~ r1_yellow_0(A_25,B_32)
      | ~ m1_subset_1(C_33,u1_struct_0(A_25))
      | ~ l1_orders_2(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_352,plain,(
    ! [A_196,B_197,C_198] :
      ( r2_lattice3(A_196,B_197,'#skF_2'(A_196,B_197,C_198))
      | k1_yellow_0(A_196,B_197) = C_198
      | ~ r2_lattice3(A_196,B_197,C_198)
      | ~ r1_yellow_0(A_196,B_197)
      | ~ m1_subset_1(C_198,u1_struct_0(A_196))
      | ~ l1_orders_2(A_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_40,plain,(
    ! [A_37,C_43,B_41] :
      ( r1_orders_2(A_37,C_43,B_41)
      | ~ r2_lattice3(A_37,k1_tarski(C_43),B_41)
      | ~ m1_subset_1(C_43,u1_struct_0(A_37))
      | ~ m1_subset_1(B_41,u1_struct_0(A_37))
      | ~ l1_orders_2(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1131,plain,(
    ! [A_408,C_409,C_410] :
      ( r1_orders_2(A_408,C_409,'#skF_2'(A_408,k1_tarski(C_409),C_410))
      | ~ m1_subset_1(C_409,u1_struct_0(A_408))
      | ~ m1_subset_1('#skF_2'(A_408,k1_tarski(C_409),C_410),u1_struct_0(A_408))
      | k1_yellow_0(A_408,k1_tarski(C_409)) = C_410
      | ~ r2_lattice3(A_408,k1_tarski(C_409),C_410)
      | ~ r1_yellow_0(A_408,k1_tarski(C_409))
      | ~ m1_subset_1(C_410,u1_struct_0(A_408))
      | ~ l1_orders_2(A_408) ) ),
    inference(resolution,[status(thm)],[c_352,c_40])).

tff(c_1141,plain,(
    ! [A_414,C_415,C_416] :
      ( r1_orders_2(A_414,C_415,'#skF_2'(A_414,k1_tarski(C_415),C_416))
      | ~ m1_subset_1(C_415,u1_struct_0(A_414))
      | k1_yellow_0(A_414,k1_tarski(C_415)) = C_416
      | ~ r2_lattice3(A_414,k1_tarski(C_415),C_416)
      | ~ r1_yellow_0(A_414,k1_tarski(C_415))
      | ~ m1_subset_1(C_416,u1_struct_0(A_414))
      | ~ l1_orders_2(A_414) ) ),
    inference(resolution,[status(thm)],[c_32,c_1131])).

tff(c_28,plain,(
    ! [A_25,C_33,B_32] :
      ( ~ r1_orders_2(A_25,C_33,'#skF_2'(A_25,B_32,C_33))
      | k1_yellow_0(A_25,B_32) = C_33
      | ~ r2_lattice3(A_25,B_32,C_33)
      | ~ r1_yellow_0(A_25,B_32)
      | ~ m1_subset_1(C_33,u1_struct_0(A_25))
      | ~ l1_orders_2(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1153,plain,(
    ! [A_417,C_418] :
      ( k1_yellow_0(A_417,k1_tarski(C_418)) = C_418
      | ~ r2_lattice3(A_417,k1_tarski(C_418),C_418)
      | ~ r1_yellow_0(A_417,k1_tarski(C_418))
      | ~ m1_subset_1(C_418,u1_struct_0(A_417))
      | ~ l1_orders_2(A_417) ) ),
    inference(resolution,[status(thm)],[c_1141,c_28])).

tff(c_1333,plain,(
    ! [A_435,B_436] :
      ( k1_yellow_0(A_435,k1_tarski(B_436)) = B_436
      | ~ r1_yellow_0(A_435,k1_tarski(B_436))
      | ~ r1_orders_2(A_435,B_436,B_436)
      | ~ m1_subset_1(B_436,u1_struct_0(A_435))
      | ~ l1_orders_2(A_435) ) ),
    inference(resolution,[status(thm)],[c_38,c_1153])).

tff(c_1338,plain,(
    ! [A_2] :
      ( k1_yellow_0('#skF_3',k1_tarski(A_2)) = A_2
      | ~ r1_orders_2('#skF_3',A_2,A_2)
      | ~ m1_subset_1(A_2,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | k1_tarski(A_2) = k1_xboole_0
      | ~ r2_hidden(A_2,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_126,c_1333])).

tff(c_1345,plain,(
    ! [A_437] :
      ( k1_yellow_0('#skF_3',k1_tarski(A_437)) = A_437
      | ~ r1_orders_2('#skF_3',A_437,A_437)
      | ~ m1_subset_1(A_437,u1_struct_0('#skF_3'))
      | k1_tarski(A_437) = k1_xboole_0
      | ~ r2_hidden(A_437,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1338])).

tff(c_1457,plain,(
    ! [B_454,C_455] :
      ( k1_yellow_0('#skF_3',k1_tarski('#skF_1'('#skF_3',B_454,C_455))) = '#skF_1'('#skF_3',B_454,C_455)
      | k1_tarski('#skF_1'('#skF_3',B_454,C_455)) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_454,C_455),'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_3',B_454,C_455),u1_struct_0('#skF_3'))
      | r2_lattice3('#skF_3',B_454,C_455)
      | ~ m1_subset_1(C_455,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_337,c_1345])).

tff(c_1461,plain,(
    ! [B_20,C_21] :
      ( k1_yellow_0('#skF_3',k1_tarski('#skF_1'('#skF_3',B_20,C_21))) = '#skF_1'('#skF_3',B_20,C_21)
      | k1_tarski('#skF_1'('#skF_3',B_20,C_21)) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_20,C_21),'#skF_4')
      | r2_lattice3('#skF_3',B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26,c_1457])).

tff(c_1465,plain,(
    ! [B_456,C_457] :
      ( k1_yellow_0('#skF_3',k1_tarski('#skF_1'('#skF_3',B_456,C_457))) = '#skF_1'('#skF_3',B_456,C_457)
      | k1_tarski('#skF_1'('#skF_3',B_456,C_457)) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_456,C_457),'#skF_4')
      | r2_lattice3('#skF_3',B_456,C_457)
      | ~ m1_subset_1(C_457,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1461])).

tff(c_52,plain,(
    ! [D_102] :
      ( r2_hidden(k1_yellow_0('#skF_3',D_102),'#skF_5')
      | k1_xboole_0 = D_102
      | ~ m1_subset_1(D_102,k1_zfmisc_1('#skF_4'))
      | ~ v1_finset_1(D_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_1477,plain,(
    ! [B_456,C_457] :
      ( r2_hidden('#skF_1'('#skF_3',B_456,C_457),'#skF_5')
      | k1_tarski('#skF_1'('#skF_3',B_456,C_457)) = k1_xboole_0
      | ~ m1_subset_1(k1_tarski('#skF_1'('#skF_3',B_456,C_457)),k1_zfmisc_1('#skF_4'))
      | ~ v1_finset_1(k1_tarski('#skF_1'('#skF_3',B_456,C_457)))
      | k1_tarski('#skF_1'('#skF_3',B_456,C_457)) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_456,C_457),'#skF_4')
      | r2_lattice3('#skF_3',B_456,C_457)
      | ~ m1_subset_1(C_457,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1465,c_52])).

tff(c_1549,plain,(
    ! [B_472,C_473] :
      ( r2_hidden('#skF_1'('#skF_3',B_472,C_473),'#skF_5')
      | ~ m1_subset_1(k1_tarski('#skF_1'('#skF_3',B_472,C_473)),k1_zfmisc_1('#skF_4'))
      | k1_tarski('#skF_1'('#skF_3',B_472,C_473)) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_472,C_473),'#skF_4')
      | r2_lattice3('#skF_3',B_472,C_473)
      | ~ m1_subset_1(C_473,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1477])).

tff(c_1558,plain,(
    ! [B_474,C_475] :
      ( r2_hidden('#skF_1'('#skF_3',B_474,C_475),'#skF_5')
      | k1_tarski('#skF_1'('#skF_3',B_474,C_475)) = k1_xboole_0
      | r2_lattice3('#skF_3',B_474,C_475)
      | ~ m1_subset_1(C_475,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'('#skF_3',B_474,C_475),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_6,c_1549])).

tff(c_102,plain,(
    ! [A_109,B_110] :
      ( m1_subset_1(k1_tarski(A_109),k1_zfmisc_1(B_110))
      | ~ r2_hidden(A_109,B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_106,plain,(
    ! [A_109,B_110] :
      ( r1_tarski(k1_tarski(A_109),B_110)
      | ~ r2_hidden(A_109,B_110) ) ),
    inference(resolution,[status(thm)],[c_102,c_8])).

tff(c_148,plain,(
    ! [A_129,B_130,D_131,C_132] :
      ( r2_lattice3(A_129,B_130,D_131)
      | ~ r2_lattice3(A_129,C_132,D_131)
      | ~ m1_subset_1(D_131,u1_struct_0(A_129))
      | ~ r1_tarski(B_130,C_132)
      | ~ l1_orders_2(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_150,plain,(
    ! [B_130] :
      ( r2_lattice3('#skF_3',B_130,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ r1_tarski(B_130,'#skF_5')
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_99,c_148])).

tff(c_153,plain,(
    ! [B_130] :
      ( r2_lattice3('#skF_3',B_130,'#skF_7')
      | ~ r1_tarski(B_130,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_150])).

tff(c_225,plain,(
    ! [A_150,C_151,B_152] :
      ( r1_orders_2(A_150,C_151,B_152)
      | ~ r2_lattice3(A_150,k1_tarski(C_151),B_152)
      | ~ m1_subset_1(C_151,u1_struct_0(A_150))
      | ~ m1_subset_1(B_152,u1_struct_0(A_150))
      | ~ l1_orders_2(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_229,plain,(
    ! [C_151] :
      ( r1_orders_2('#skF_3',C_151,'#skF_7')
      | ~ m1_subset_1(C_151,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ r1_tarski(k1_tarski(C_151),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_153,c_225])).

tff(c_233,plain,(
    ! [C_153] :
      ( r1_orders_2('#skF_3',C_153,'#skF_7')
      | ~ m1_subset_1(C_153,u1_struct_0('#skF_3'))
      | ~ r1_tarski(k1_tarski(C_153),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_229])).

tff(c_239,plain,(
    ! [A_154] :
      ( r1_orders_2('#skF_3',A_154,'#skF_7')
      | ~ m1_subset_1(A_154,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_154,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_106,c_233])).

tff(c_243,plain,(
    ! [B_20,C_21] :
      ( r1_orders_2('#skF_3','#skF_1'('#skF_3',B_20,C_21),'#skF_7')
      | ~ r2_hidden('#skF_1'('#skF_3',B_20,C_21),'#skF_5')
      | r2_lattice3('#skF_3',B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26,c_239])).

tff(c_312,plain,(
    ! [B_179,C_180] :
      ( r1_orders_2('#skF_3','#skF_1'('#skF_3',B_179,C_180),'#skF_7')
      | ~ r2_hidden('#skF_1'('#skF_3',B_179,C_180),'#skF_5')
      | r2_lattice3('#skF_3',B_179,C_180)
      | ~ m1_subset_1(C_180,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_243])).

tff(c_22,plain,(
    ! [A_13,B_20,C_21] :
      ( ~ r1_orders_2(A_13,'#skF_1'(A_13,B_20,C_21),C_21)
      | r2_lattice3(A_13,B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0(A_13))
      | ~ l1_orders_2(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_316,plain,(
    ! [B_179] :
      ( ~ l1_orders_2('#skF_3')
      | ~ r2_hidden('#skF_1'('#skF_3',B_179,'#skF_7'),'#skF_5')
      | r2_lattice3('#skF_3',B_179,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_312,c_22])).

tff(c_319,plain,(
    ! [B_179] :
      ( ~ r2_hidden('#skF_1'('#skF_3',B_179,'#skF_7'),'#skF_5')
      | r2_lattice3('#skF_3',B_179,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_60,c_316])).

tff(c_1564,plain,(
    ! [B_474] :
      ( k1_tarski('#skF_1'('#skF_3',B_474,'#skF_7')) = k1_xboole_0
      | r2_lattice3('#skF_3',B_474,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'('#skF_3',B_474,'#skF_7'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1558,c_319])).

tff(c_1575,plain,(
    ! [B_476] :
      ( k1_tarski('#skF_1'('#skF_3',B_476,'#skF_7')) = k1_xboole_0
      | r2_lattice3('#skF_3',B_476,'#skF_7')
      | ~ r2_hidden('#skF_1'('#skF_3',B_476,'#skF_7'),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1564])).

tff(c_1579,plain,
    ( k1_tarski('#skF_1'('#skF_3','#skF_4','#skF_7')) = k1_xboole_0
    | r2_lattice3('#skF_3','#skF_4','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_1575])).

tff(c_1582,plain,
    ( k1_tarski('#skF_1'('#skF_3','#skF_4','#skF_7')) = k1_xboole_0
    | r2_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_1579])).

tff(c_1583,plain,(
    k1_tarski('#skF_1'('#skF_3','#skF_4','#skF_7')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_1582])).

tff(c_4,plain,(
    ! [A_1] : ~ v1_xboole_0(k1_tarski(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1701,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1583,c_4])).

tff(c_1742,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1701])).

tff(c_1744,plain,(
    ~ r2_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_1780,plain,(
    ! [D_487] :
      ( m1_subset_1('#skF_6'(D_487),k1_zfmisc_1('#skF_4'))
      | ~ r2_hidden(D_487,'#skF_5')
      | ~ m1_subset_1(D_487,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_1788,plain,(
    ! [D_487] :
      ( r1_tarski('#skF_6'(D_487),'#skF_4')
      | ~ r2_hidden(D_487,'#skF_5')
      | ~ m1_subset_1(D_487,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1780,c_8])).

tff(c_78,plain,(
    ! [D_100] :
      ( r1_yellow_0('#skF_3','#skF_6'(D_100))
      | ~ r2_hidden(D_100,'#skF_5')
      | ~ m1_subset_1(D_100,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_1743,plain,(
    r2_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_1792,plain,(
    ! [A_493,B_494,D_495,C_496] :
      ( r2_lattice3(A_493,B_494,D_495)
      | ~ r2_lattice3(A_493,C_496,D_495)
      | ~ m1_subset_1(D_495,u1_struct_0(A_493))
      | ~ r1_tarski(B_494,C_496)
      | ~ l1_orders_2(A_493) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1794,plain,(
    ! [B_494] :
      ( r2_lattice3('#skF_3',B_494,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ r1_tarski(B_494,'#skF_4')
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1743,c_1792])).

tff(c_1797,plain,(
    ! [B_494] :
      ( r2_lattice3('#skF_3',B_494,'#skF_7')
      | ~ r1_tarski(B_494,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_1794])).

tff(c_1832,plain,(
    ! [A_502,B_503,C_504] :
      ( m1_subset_1('#skF_1'(A_502,B_503,C_504),u1_struct_0(A_502))
      | r2_lattice3(A_502,B_503,C_504)
      | ~ m1_subset_1(C_504,u1_struct_0(A_502))
      | ~ l1_orders_2(A_502) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_76,plain,(
    ! [D_100] :
      ( k1_yellow_0('#skF_3','#skF_6'(D_100)) = D_100
      | ~ r2_hidden(D_100,'#skF_5')
      | ~ m1_subset_1(D_100,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_1836,plain,(
    ! [B_503,C_504] :
      ( k1_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_503,C_504))) = '#skF_1'('#skF_3',B_503,C_504)
      | ~ r2_hidden('#skF_1'('#skF_3',B_503,C_504),'#skF_5')
      | r2_lattice3('#skF_3',B_503,C_504)
      | ~ m1_subset_1(C_504,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1832,c_76])).

tff(c_1843,plain,(
    ! [B_503,C_504] :
      ( k1_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_503,C_504))) = '#skF_1'('#skF_3',B_503,C_504)
      | ~ r2_hidden('#skF_1'('#skF_3',B_503,C_504),'#skF_5')
      | r2_lattice3('#skF_3',B_503,C_504)
      | ~ m1_subset_1(C_504,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1836])).

tff(c_2177,plain,(
    ! [B_614,C_615] :
      ( k1_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_614,C_615))) = '#skF_1'('#skF_3',B_614,C_615)
      | ~ r2_hidden('#skF_1'('#skF_3',B_614,C_615),'#skF_5')
      | r2_lattice3('#skF_3',B_614,C_615)
      | ~ m1_subset_1(C_615,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1836])).

tff(c_34,plain,(
    ! [A_25,B_32,D_36] :
      ( r1_orders_2(A_25,k1_yellow_0(A_25,B_32),D_36)
      | ~ r2_lattice3(A_25,B_32,D_36)
      | ~ m1_subset_1(D_36,u1_struct_0(A_25))
      | ~ r1_yellow_0(A_25,B_32)
      | ~ m1_subset_1(k1_yellow_0(A_25,B_32),u1_struct_0(A_25))
      | ~ l1_orders_2(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2182,plain,(
    ! [B_614,C_615,D_36] :
      ( r1_orders_2('#skF_3',k1_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_614,C_615))),D_36)
      | ~ r2_lattice3('#skF_3','#skF_6'('#skF_1'('#skF_3',B_614,C_615)),D_36)
      | ~ m1_subset_1(D_36,u1_struct_0('#skF_3'))
      | ~ r1_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_614,C_615)))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_614,C_615),u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ r2_hidden('#skF_1'('#skF_3',B_614,C_615),'#skF_5')
      | r2_lattice3('#skF_3',B_614,C_615)
      | ~ m1_subset_1(C_615,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2177,c_34])).

tff(c_3595,plain,(
    ! [B_946,C_947,D_948] :
      ( r1_orders_2('#skF_3',k1_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_946,C_947))),D_948)
      | ~ r2_lattice3('#skF_3','#skF_6'('#skF_1'('#skF_3',B_946,C_947)),D_948)
      | ~ m1_subset_1(D_948,u1_struct_0('#skF_3'))
      | ~ r1_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_946,C_947)))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_946,C_947),u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'('#skF_3',B_946,C_947),'#skF_5')
      | r2_lattice3('#skF_3',B_946,C_947)
      | ~ m1_subset_1(C_947,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2182])).

tff(c_4916,plain,(
    ! [B_1322,C_1323,D_1324] :
      ( r1_orders_2('#skF_3','#skF_1'('#skF_3',B_1322,C_1323),D_1324)
      | ~ r2_lattice3('#skF_3','#skF_6'('#skF_1'('#skF_3',B_1322,C_1323)),D_1324)
      | ~ m1_subset_1(D_1324,u1_struct_0('#skF_3'))
      | ~ r1_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_1322,C_1323)))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_1322,C_1323),u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'('#skF_3',B_1322,C_1323),'#skF_5')
      | r2_lattice3('#skF_3',B_1322,C_1323)
      | ~ m1_subset_1(C_1323,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'('#skF_3',B_1322,C_1323),'#skF_5')
      | r2_lattice3('#skF_3',B_1322,C_1323)
      | ~ m1_subset_1(C_1323,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1843,c_3595])).

tff(c_4958,plain,(
    ! [B_1322,C_1323] :
      ( r1_orders_2('#skF_3','#skF_1'('#skF_3',B_1322,C_1323),'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ r1_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_1322,C_1323)))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_1322,C_1323),u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'('#skF_3',B_1322,C_1323),'#skF_5')
      | r2_lattice3('#skF_3',B_1322,C_1323)
      | ~ m1_subset_1(C_1323,u1_struct_0('#skF_3'))
      | ~ r1_tarski('#skF_6'('#skF_1'('#skF_3',B_1322,C_1323)),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1797,c_4916])).

tff(c_4988,plain,(
    ! [B_1325,C_1326] :
      ( r1_orders_2('#skF_3','#skF_1'('#skF_3',B_1325,C_1326),'#skF_7')
      | ~ r1_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_1325,C_1326)))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_1325,C_1326),u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'('#skF_3',B_1325,C_1326),'#skF_5')
      | r2_lattice3('#skF_3',B_1325,C_1326)
      | ~ m1_subset_1(C_1326,u1_struct_0('#skF_3'))
      | ~ r1_tarski('#skF_6'('#skF_1'('#skF_3',B_1325,C_1326)),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_4958])).

tff(c_4997,plain,(
    ! [B_1327,C_1328] :
      ( r1_orders_2('#skF_3','#skF_1'('#skF_3',B_1327,C_1328),'#skF_7')
      | r2_lattice3('#skF_3',B_1327,C_1328)
      | ~ m1_subset_1(C_1328,u1_struct_0('#skF_3'))
      | ~ r1_tarski('#skF_6'('#skF_1'('#skF_3',B_1327,C_1328)),'#skF_4')
      | ~ r2_hidden('#skF_1'('#skF_3',B_1327,C_1328),'#skF_5')
      | ~ m1_subset_1('#skF_1'('#skF_3',B_1327,C_1328),u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_78,c_4988])).

tff(c_5002,plain,(
    ! [B_1329,C_1330] :
      ( r1_orders_2('#skF_3','#skF_1'('#skF_3',B_1329,C_1330),'#skF_7')
      | r2_lattice3('#skF_3',B_1329,C_1330)
      | ~ m1_subset_1(C_1330,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'('#skF_3',B_1329,C_1330),'#skF_5')
      | ~ m1_subset_1('#skF_1'('#skF_3',B_1329,C_1330),u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1788,c_4997])).

tff(c_5006,plain,(
    ! [B_20,C_21] :
      ( r1_orders_2('#skF_3','#skF_1'('#skF_3',B_20,C_21),'#skF_7')
      | ~ r2_hidden('#skF_1'('#skF_3',B_20,C_21),'#skF_5')
      | r2_lattice3('#skF_3',B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26,c_5002])).

tff(c_5010,plain,(
    ! [B_1331,C_1332] :
      ( r1_orders_2('#skF_3','#skF_1'('#skF_3',B_1331,C_1332),'#skF_7')
      | ~ r2_hidden('#skF_1'('#skF_3',B_1331,C_1332),'#skF_5')
      | r2_lattice3('#skF_3',B_1331,C_1332)
      | ~ m1_subset_1(C_1332,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_5006])).

tff(c_5018,plain,(
    ! [B_1331] :
      ( ~ l1_orders_2('#skF_3')
      | ~ r2_hidden('#skF_1'('#skF_3',B_1331,'#skF_7'),'#skF_5')
      | r2_lattice3('#skF_3',B_1331,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_5010,c_22])).

tff(c_5028,plain,(
    ! [B_1333] :
      ( ~ r2_hidden('#skF_1'('#skF_3',B_1333,'#skF_7'),'#skF_5')
      | r2_lattice3('#skF_3',B_1333,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_60,c_5018])).

tff(c_5036,plain,
    ( r2_lattice3('#skF_3','#skF_5','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_5028])).

tff(c_5042,plain,(
    r2_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_5036])).

tff(c_5044,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1744,c_5042])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:49:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.93/2.82  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.93/2.83  
% 7.93/2.83  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.93/2.83  %$ r3_orders_2 > r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_finset_1 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_6
% 7.93/2.83  
% 7.93/2.83  %Foreground sorts:
% 7.93/2.83  
% 7.93/2.83  
% 7.93/2.83  %Background operators:
% 7.93/2.83  
% 7.93/2.83  
% 7.93/2.83  %Foreground operators:
% 7.93/2.83  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.93/2.83  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 7.93/2.83  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 7.93/2.83  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.93/2.83  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 7.93/2.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.93/2.83  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.93/2.83  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.93/2.83  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 7.93/2.83  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.93/2.83  tff('#skF_7', type, '#skF_7': $i).
% 7.93/2.83  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.93/2.83  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 7.93/2.83  tff('#skF_5', type, '#skF_5': $i).
% 7.93/2.83  tff('#skF_3', type, '#skF_3': $i).
% 7.93/2.83  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.93/2.83  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 7.93/2.83  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 7.93/2.83  tff(r1_yellow_0, type, r1_yellow_0: ($i * $i) > $o).
% 7.93/2.83  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.93/2.83  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 7.93/2.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.93/2.83  tff('#skF_4', type, '#skF_4': $i).
% 7.93/2.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.93/2.83  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.93/2.83  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.93/2.83  tff(v1_finset_1, type, v1_finset_1: $i > $o).
% 7.93/2.83  tff('#skF_6', type, '#skF_6': $i > $i).
% 7.93/2.83  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.93/2.83  
% 8.27/2.85  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 8.27/2.85  tff(f_198, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((((![D]: ((v1_finset_1(D) & m1_subset_1(D, k1_zfmisc_1(B))) => (~(D = k1_xboole_0) => r1_yellow_0(A, D)))) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => ~(r2_hidden(D, C) & (![E]: ((v1_finset_1(E) & m1_subset_1(E, k1_zfmisc_1(B))) => ~(r1_yellow_0(A, E) & (D = k1_yellow_0(A, E))))))))) & (![D]: ((v1_finset_1(D) & m1_subset_1(D, k1_zfmisc_1(B))) => (~(D = k1_xboole_0) => r2_hidden(k1_yellow_0(A, D), C))))) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, B, D) <=> r2_lattice3(A, C, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_waybel_0)).
% 8.27/2.85  tff(f_81, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, D, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_lattice3)).
% 8.27/2.86  tff(f_33, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 8.27/2.86  tff(f_39, axiom, (![A]: v1_finset_1(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_finset_1)).
% 8.27/2.86  tff(f_67, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => r3_orders_2(A, B, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r3_orders_2)).
% 8.27/2.86  tff(f_54, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 8.27/2.86  tff(f_123, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((((r1_lattice3(A, k1_tarski(C), B) => r1_orders_2(A, B, C)) & (r1_orders_2(A, B, C) => r1_lattice3(A, k1_tarski(C), B))) & (r2_lattice3(A, k1_tarski(C), B) => r1_orders_2(A, C, B))) & (r1_orders_2(A, C, B) => r2_lattice3(A, k1_tarski(C), B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_yellow_0)).
% 8.27/2.86  tff(f_99, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_yellow_0(A, B) => ((C = k1_yellow_0(A, B)) <=> (r2_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, B, D) => r1_orders_2(A, C, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_yellow_0)).
% 8.27/2.86  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 8.27/2.86  tff(f_139, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (r1_tarski(B, C) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r1_lattice3(A, C, D) => r1_lattice3(A, B, D)) & (r2_lattice3(A, C, D) => r2_lattice3(A, B, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_yellow_0)).
% 8.27/2.86  tff(f_29, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 8.27/2.86  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 8.27/2.86  tff(c_74, plain, (r2_lattice3('#skF_3', '#skF_4', '#skF_7') | r2_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_198])).
% 8.27/2.86  tff(c_99, plain, (r2_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(splitLeft, [status(thm)], [c_74])).
% 8.27/2.86  tff(c_68, plain, (~r2_lattice3('#skF_3', '#skF_5', '#skF_7') | ~r2_lattice3('#skF_3', '#skF_4', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_198])).
% 8.27/2.86  tff(c_101, plain, (~r2_lattice3('#skF_3', '#skF_4', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_99, c_68])).
% 8.27/2.86  tff(c_60, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_198])).
% 8.27/2.86  tff(c_50, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_198])).
% 8.27/2.86  tff(c_24, plain, (![A_13, B_20, C_21]: (r2_hidden('#skF_1'(A_13, B_20, C_21), B_20) | r2_lattice3(A_13, B_20, C_21) | ~m1_subset_1(C_21, u1_struct_0(A_13)) | ~l1_orders_2(A_13))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.27/2.86  tff(c_6, plain, (![A_2, B_3]: (m1_subset_1(k1_tarski(A_2), k1_zfmisc_1(B_3)) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.27/2.86  tff(c_12, plain, (![A_6]: (v1_finset_1(k1_tarski(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.27/2.86  tff(c_26, plain, (![A_13, B_20, C_21]: (m1_subset_1('#skF_1'(A_13, B_20, C_21), u1_struct_0(A_13)) | r2_lattice3(A_13, B_20, C_21) | ~m1_subset_1(C_21, u1_struct_0(A_13)) | ~l1_orders_2(A_13))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.27/2.86  tff(c_66, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_198])).
% 8.27/2.86  tff(c_64, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_198])).
% 8.27/2.86  tff(c_205, plain, (![A_146, B_147, C_148]: (r3_orders_2(A_146, B_147, B_147) | ~m1_subset_1(C_148, u1_struct_0(A_146)) | ~m1_subset_1(B_147, u1_struct_0(A_146)) | ~l1_orders_2(A_146) | ~v3_orders_2(A_146) | v2_struct_0(A_146))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.27/2.86  tff(c_209, plain, (![B_147]: (r3_orders_2('#skF_3', B_147, B_147) | ~m1_subset_1(B_147, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_205])).
% 8.27/2.86  tff(c_213, plain, (![B_147]: (r3_orders_2('#skF_3', B_147, B_147) | ~m1_subset_1(B_147, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_209])).
% 8.27/2.86  tff(c_215, plain, (![B_149]: (r3_orders_2('#skF_3', B_149, B_149) | ~m1_subset_1(B_149, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_66, c_213])).
% 8.27/2.86  tff(c_218, plain, (![B_20, C_21]: (r3_orders_2('#skF_3', '#skF_1'('#skF_3', B_20, C_21), '#skF_1'('#skF_3', B_20, C_21)) | r2_lattice3('#skF_3', B_20, C_21) | ~m1_subset_1(C_21, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_26, c_215])).
% 8.27/2.86  tff(c_223, plain, (![B_20, C_21]: (r3_orders_2('#skF_3', '#skF_1'('#skF_3', B_20, C_21), '#skF_1'('#skF_3', B_20, C_21)) | r2_lattice3('#skF_3', B_20, C_21) | ~m1_subset_1(C_21, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_218])).
% 8.27/2.86  tff(c_329, plain, (![A_185, B_186, C_187]: (r1_orders_2(A_185, B_186, C_187) | ~r3_orders_2(A_185, B_186, C_187) | ~m1_subset_1(C_187, u1_struct_0(A_185)) | ~m1_subset_1(B_186, u1_struct_0(A_185)) | ~l1_orders_2(A_185) | ~v3_orders_2(A_185) | v2_struct_0(A_185))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.27/2.86  tff(c_331, plain, (![B_20, C_21]: (r1_orders_2('#skF_3', '#skF_1'('#skF_3', B_20, C_21), '#skF_1'('#skF_3', B_20, C_21)) | ~m1_subset_1('#skF_1'('#skF_3', B_20, C_21), u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3') | r2_lattice3('#skF_3', B_20, C_21) | ~m1_subset_1(C_21, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_223, c_329])).
% 8.27/2.86  tff(c_336, plain, (![B_20, C_21]: (r1_orders_2('#skF_3', '#skF_1'('#skF_3', B_20, C_21), '#skF_1'('#skF_3', B_20, C_21)) | ~m1_subset_1('#skF_1'('#skF_3', B_20, C_21), u1_struct_0('#skF_3')) | v2_struct_0('#skF_3') | r2_lattice3('#skF_3', B_20, C_21) | ~m1_subset_1(C_21, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_331])).
% 8.27/2.86  tff(c_337, plain, (![B_20, C_21]: (r1_orders_2('#skF_3', '#skF_1'('#skF_3', B_20, C_21), '#skF_1'('#skF_3', B_20, C_21)) | ~m1_subset_1('#skF_1'('#skF_3', B_20, C_21), u1_struct_0('#skF_3')) | r2_lattice3('#skF_3', B_20, C_21) | ~m1_subset_1(C_21, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_66, c_336])).
% 8.27/2.86  tff(c_115, plain, (![D_115]: (r1_yellow_0('#skF_3', D_115) | k1_xboole_0=D_115 | ~m1_subset_1(D_115, k1_zfmisc_1('#skF_4')) | ~v1_finset_1(D_115))), inference(cnfTransformation, [status(thm)], [f_198])).
% 8.27/2.86  tff(c_119, plain, (![A_2]: (r1_yellow_0('#skF_3', k1_tarski(A_2)) | k1_tarski(A_2)=k1_xboole_0 | ~v1_finset_1(k1_tarski(A_2)) | ~r2_hidden(A_2, '#skF_4'))), inference(resolution, [status(thm)], [c_6, c_115])).
% 8.27/2.86  tff(c_126, plain, (![A_2]: (r1_yellow_0('#skF_3', k1_tarski(A_2)) | k1_tarski(A_2)=k1_xboole_0 | ~r2_hidden(A_2, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_119])).
% 8.27/2.86  tff(c_38, plain, (![A_37, C_43, B_41]: (r2_lattice3(A_37, k1_tarski(C_43), B_41) | ~r1_orders_2(A_37, C_43, B_41) | ~m1_subset_1(C_43, u1_struct_0(A_37)) | ~m1_subset_1(B_41, u1_struct_0(A_37)) | ~l1_orders_2(A_37))), inference(cnfTransformation, [status(thm)], [f_123])).
% 8.27/2.86  tff(c_32, plain, (![A_25, B_32, C_33]: (m1_subset_1('#skF_2'(A_25, B_32, C_33), u1_struct_0(A_25)) | k1_yellow_0(A_25, B_32)=C_33 | ~r2_lattice3(A_25, B_32, C_33) | ~r1_yellow_0(A_25, B_32) | ~m1_subset_1(C_33, u1_struct_0(A_25)) | ~l1_orders_2(A_25))), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.27/2.86  tff(c_352, plain, (![A_196, B_197, C_198]: (r2_lattice3(A_196, B_197, '#skF_2'(A_196, B_197, C_198)) | k1_yellow_0(A_196, B_197)=C_198 | ~r2_lattice3(A_196, B_197, C_198) | ~r1_yellow_0(A_196, B_197) | ~m1_subset_1(C_198, u1_struct_0(A_196)) | ~l1_orders_2(A_196))), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.27/2.86  tff(c_40, plain, (![A_37, C_43, B_41]: (r1_orders_2(A_37, C_43, B_41) | ~r2_lattice3(A_37, k1_tarski(C_43), B_41) | ~m1_subset_1(C_43, u1_struct_0(A_37)) | ~m1_subset_1(B_41, u1_struct_0(A_37)) | ~l1_orders_2(A_37))), inference(cnfTransformation, [status(thm)], [f_123])).
% 8.27/2.86  tff(c_1131, plain, (![A_408, C_409, C_410]: (r1_orders_2(A_408, C_409, '#skF_2'(A_408, k1_tarski(C_409), C_410)) | ~m1_subset_1(C_409, u1_struct_0(A_408)) | ~m1_subset_1('#skF_2'(A_408, k1_tarski(C_409), C_410), u1_struct_0(A_408)) | k1_yellow_0(A_408, k1_tarski(C_409))=C_410 | ~r2_lattice3(A_408, k1_tarski(C_409), C_410) | ~r1_yellow_0(A_408, k1_tarski(C_409)) | ~m1_subset_1(C_410, u1_struct_0(A_408)) | ~l1_orders_2(A_408))), inference(resolution, [status(thm)], [c_352, c_40])).
% 8.27/2.86  tff(c_1141, plain, (![A_414, C_415, C_416]: (r1_orders_2(A_414, C_415, '#skF_2'(A_414, k1_tarski(C_415), C_416)) | ~m1_subset_1(C_415, u1_struct_0(A_414)) | k1_yellow_0(A_414, k1_tarski(C_415))=C_416 | ~r2_lattice3(A_414, k1_tarski(C_415), C_416) | ~r1_yellow_0(A_414, k1_tarski(C_415)) | ~m1_subset_1(C_416, u1_struct_0(A_414)) | ~l1_orders_2(A_414))), inference(resolution, [status(thm)], [c_32, c_1131])).
% 8.27/2.86  tff(c_28, plain, (![A_25, C_33, B_32]: (~r1_orders_2(A_25, C_33, '#skF_2'(A_25, B_32, C_33)) | k1_yellow_0(A_25, B_32)=C_33 | ~r2_lattice3(A_25, B_32, C_33) | ~r1_yellow_0(A_25, B_32) | ~m1_subset_1(C_33, u1_struct_0(A_25)) | ~l1_orders_2(A_25))), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.27/2.86  tff(c_1153, plain, (![A_417, C_418]: (k1_yellow_0(A_417, k1_tarski(C_418))=C_418 | ~r2_lattice3(A_417, k1_tarski(C_418), C_418) | ~r1_yellow_0(A_417, k1_tarski(C_418)) | ~m1_subset_1(C_418, u1_struct_0(A_417)) | ~l1_orders_2(A_417))), inference(resolution, [status(thm)], [c_1141, c_28])).
% 8.27/2.86  tff(c_1333, plain, (![A_435, B_436]: (k1_yellow_0(A_435, k1_tarski(B_436))=B_436 | ~r1_yellow_0(A_435, k1_tarski(B_436)) | ~r1_orders_2(A_435, B_436, B_436) | ~m1_subset_1(B_436, u1_struct_0(A_435)) | ~l1_orders_2(A_435))), inference(resolution, [status(thm)], [c_38, c_1153])).
% 8.27/2.86  tff(c_1338, plain, (![A_2]: (k1_yellow_0('#skF_3', k1_tarski(A_2))=A_2 | ~r1_orders_2('#skF_3', A_2, A_2) | ~m1_subset_1(A_2, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | k1_tarski(A_2)=k1_xboole_0 | ~r2_hidden(A_2, '#skF_4'))), inference(resolution, [status(thm)], [c_126, c_1333])).
% 8.27/2.86  tff(c_1345, plain, (![A_437]: (k1_yellow_0('#skF_3', k1_tarski(A_437))=A_437 | ~r1_orders_2('#skF_3', A_437, A_437) | ~m1_subset_1(A_437, u1_struct_0('#skF_3')) | k1_tarski(A_437)=k1_xboole_0 | ~r2_hidden(A_437, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1338])).
% 8.27/2.86  tff(c_1457, plain, (![B_454, C_455]: (k1_yellow_0('#skF_3', k1_tarski('#skF_1'('#skF_3', B_454, C_455)))='#skF_1'('#skF_3', B_454, C_455) | k1_tarski('#skF_1'('#skF_3', B_454, C_455))=k1_xboole_0 | ~r2_hidden('#skF_1'('#skF_3', B_454, C_455), '#skF_4') | ~m1_subset_1('#skF_1'('#skF_3', B_454, C_455), u1_struct_0('#skF_3')) | r2_lattice3('#skF_3', B_454, C_455) | ~m1_subset_1(C_455, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_337, c_1345])).
% 8.27/2.86  tff(c_1461, plain, (![B_20, C_21]: (k1_yellow_0('#skF_3', k1_tarski('#skF_1'('#skF_3', B_20, C_21)))='#skF_1'('#skF_3', B_20, C_21) | k1_tarski('#skF_1'('#skF_3', B_20, C_21))=k1_xboole_0 | ~r2_hidden('#skF_1'('#skF_3', B_20, C_21), '#skF_4') | r2_lattice3('#skF_3', B_20, C_21) | ~m1_subset_1(C_21, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_26, c_1457])).
% 8.27/2.86  tff(c_1465, plain, (![B_456, C_457]: (k1_yellow_0('#skF_3', k1_tarski('#skF_1'('#skF_3', B_456, C_457)))='#skF_1'('#skF_3', B_456, C_457) | k1_tarski('#skF_1'('#skF_3', B_456, C_457))=k1_xboole_0 | ~r2_hidden('#skF_1'('#skF_3', B_456, C_457), '#skF_4') | r2_lattice3('#skF_3', B_456, C_457) | ~m1_subset_1(C_457, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1461])).
% 8.27/2.86  tff(c_52, plain, (![D_102]: (r2_hidden(k1_yellow_0('#skF_3', D_102), '#skF_5') | k1_xboole_0=D_102 | ~m1_subset_1(D_102, k1_zfmisc_1('#skF_4')) | ~v1_finset_1(D_102))), inference(cnfTransformation, [status(thm)], [f_198])).
% 8.27/2.86  tff(c_1477, plain, (![B_456, C_457]: (r2_hidden('#skF_1'('#skF_3', B_456, C_457), '#skF_5') | k1_tarski('#skF_1'('#skF_3', B_456, C_457))=k1_xboole_0 | ~m1_subset_1(k1_tarski('#skF_1'('#skF_3', B_456, C_457)), k1_zfmisc_1('#skF_4')) | ~v1_finset_1(k1_tarski('#skF_1'('#skF_3', B_456, C_457))) | k1_tarski('#skF_1'('#skF_3', B_456, C_457))=k1_xboole_0 | ~r2_hidden('#skF_1'('#skF_3', B_456, C_457), '#skF_4') | r2_lattice3('#skF_3', B_456, C_457) | ~m1_subset_1(C_457, u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1465, c_52])).
% 8.27/2.86  tff(c_1549, plain, (![B_472, C_473]: (r2_hidden('#skF_1'('#skF_3', B_472, C_473), '#skF_5') | ~m1_subset_1(k1_tarski('#skF_1'('#skF_3', B_472, C_473)), k1_zfmisc_1('#skF_4')) | k1_tarski('#skF_1'('#skF_3', B_472, C_473))=k1_xboole_0 | ~r2_hidden('#skF_1'('#skF_3', B_472, C_473), '#skF_4') | r2_lattice3('#skF_3', B_472, C_473) | ~m1_subset_1(C_473, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1477])).
% 8.27/2.86  tff(c_1558, plain, (![B_474, C_475]: (r2_hidden('#skF_1'('#skF_3', B_474, C_475), '#skF_5') | k1_tarski('#skF_1'('#skF_3', B_474, C_475))=k1_xboole_0 | r2_lattice3('#skF_3', B_474, C_475) | ~m1_subset_1(C_475, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_1'('#skF_3', B_474, C_475), '#skF_4'))), inference(resolution, [status(thm)], [c_6, c_1549])).
% 8.27/2.86  tff(c_102, plain, (![A_109, B_110]: (m1_subset_1(k1_tarski(A_109), k1_zfmisc_1(B_110)) | ~r2_hidden(A_109, B_110))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.27/2.86  tff(c_8, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.27/2.86  tff(c_106, plain, (![A_109, B_110]: (r1_tarski(k1_tarski(A_109), B_110) | ~r2_hidden(A_109, B_110))), inference(resolution, [status(thm)], [c_102, c_8])).
% 8.27/2.86  tff(c_148, plain, (![A_129, B_130, D_131, C_132]: (r2_lattice3(A_129, B_130, D_131) | ~r2_lattice3(A_129, C_132, D_131) | ~m1_subset_1(D_131, u1_struct_0(A_129)) | ~r1_tarski(B_130, C_132) | ~l1_orders_2(A_129))), inference(cnfTransformation, [status(thm)], [f_139])).
% 8.27/2.86  tff(c_150, plain, (![B_130]: (r2_lattice3('#skF_3', B_130, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~r1_tarski(B_130, '#skF_5') | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_99, c_148])).
% 8.27/2.86  tff(c_153, plain, (![B_130]: (r2_lattice3('#skF_3', B_130, '#skF_7') | ~r1_tarski(B_130, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_150])).
% 8.27/2.86  tff(c_225, plain, (![A_150, C_151, B_152]: (r1_orders_2(A_150, C_151, B_152) | ~r2_lattice3(A_150, k1_tarski(C_151), B_152) | ~m1_subset_1(C_151, u1_struct_0(A_150)) | ~m1_subset_1(B_152, u1_struct_0(A_150)) | ~l1_orders_2(A_150))), inference(cnfTransformation, [status(thm)], [f_123])).
% 8.27/2.86  tff(c_229, plain, (![C_151]: (r1_orders_2('#skF_3', C_151, '#skF_7') | ~m1_subset_1(C_151, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~r1_tarski(k1_tarski(C_151), '#skF_5'))), inference(resolution, [status(thm)], [c_153, c_225])).
% 8.27/2.86  tff(c_233, plain, (![C_153]: (r1_orders_2('#skF_3', C_153, '#skF_7') | ~m1_subset_1(C_153, u1_struct_0('#skF_3')) | ~r1_tarski(k1_tarski(C_153), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_229])).
% 8.27/2.86  tff(c_239, plain, (![A_154]: (r1_orders_2('#skF_3', A_154, '#skF_7') | ~m1_subset_1(A_154, u1_struct_0('#skF_3')) | ~r2_hidden(A_154, '#skF_5'))), inference(resolution, [status(thm)], [c_106, c_233])).
% 8.27/2.86  tff(c_243, plain, (![B_20, C_21]: (r1_orders_2('#skF_3', '#skF_1'('#skF_3', B_20, C_21), '#skF_7') | ~r2_hidden('#skF_1'('#skF_3', B_20, C_21), '#skF_5') | r2_lattice3('#skF_3', B_20, C_21) | ~m1_subset_1(C_21, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_26, c_239])).
% 8.27/2.86  tff(c_312, plain, (![B_179, C_180]: (r1_orders_2('#skF_3', '#skF_1'('#skF_3', B_179, C_180), '#skF_7') | ~r2_hidden('#skF_1'('#skF_3', B_179, C_180), '#skF_5') | r2_lattice3('#skF_3', B_179, C_180) | ~m1_subset_1(C_180, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_243])).
% 8.27/2.86  tff(c_22, plain, (![A_13, B_20, C_21]: (~r1_orders_2(A_13, '#skF_1'(A_13, B_20, C_21), C_21) | r2_lattice3(A_13, B_20, C_21) | ~m1_subset_1(C_21, u1_struct_0(A_13)) | ~l1_orders_2(A_13))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.27/2.86  tff(c_316, plain, (![B_179]: (~l1_orders_2('#skF_3') | ~r2_hidden('#skF_1'('#skF_3', B_179, '#skF_7'), '#skF_5') | r2_lattice3('#skF_3', B_179, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_312, c_22])).
% 8.27/2.86  tff(c_319, plain, (![B_179]: (~r2_hidden('#skF_1'('#skF_3', B_179, '#skF_7'), '#skF_5') | r2_lattice3('#skF_3', B_179, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_60, c_316])).
% 8.27/2.86  tff(c_1564, plain, (![B_474]: (k1_tarski('#skF_1'('#skF_3', B_474, '#skF_7'))=k1_xboole_0 | r2_lattice3('#skF_3', B_474, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~r2_hidden('#skF_1'('#skF_3', B_474, '#skF_7'), '#skF_4'))), inference(resolution, [status(thm)], [c_1558, c_319])).
% 8.27/2.86  tff(c_1575, plain, (![B_476]: (k1_tarski('#skF_1'('#skF_3', B_476, '#skF_7'))=k1_xboole_0 | r2_lattice3('#skF_3', B_476, '#skF_7') | ~r2_hidden('#skF_1'('#skF_3', B_476, '#skF_7'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1564])).
% 8.27/2.86  tff(c_1579, plain, (k1_tarski('#skF_1'('#skF_3', '#skF_4', '#skF_7'))=k1_xboole_0 | r2_lattice3('#skF_3', '#skF_4', '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_24, c_1575])).
% 8.27/2.86  tff(c_1582, plain, (k1_tarski('#skF_1'('#skF_3', '#skF_4', '#skF_7'))=k1_xboole_0 | r2_lattice3('#skF_3', '#skF_4', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_1579])).
% 8.27/2.86  tff(c_1583, plain, (k1_tarski('#skF_1'('#skF_3', '#skF_4', '#skF_7'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_101, c_1582])).
% 8.27/2.86  tff(c_4, plain, (![A_1]: (~v1_xboole_0(k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.27/2.86  tff(c_1701, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1583, c_4])).
% 8.27/2.86  tff(c_1742, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_1701])).
% 8.27/2.86  tff(c_1744, plain, (~r2_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_74])).
% 8.27/2.86  tff(c_1780, plain, (![D_487]: (m1_subset_1('#skF_6'(D_487), k1_zfmisc_1('#skF_4')) | ~r2_hidden(D_487, '#skF_5') | ~m1_subset_1(D_487, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_198])).
% 8.27/2.86  tff(c_1788, plain, (![D_487]: (r1_tarski('#skF_6'(D_487), '#skF_4') | ~r2_hidden(D_487, '#skF_5') | ~m1_subset_1(D_487, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_1780, c_8])).
% 8.27/2.86  tff(c_78, plain, (![D_100]: (r1_yellow_0('#skF_3', '#skF_6'(D_100)) | ~r2_hidden(D_100, '#skF_5') | ~m1_subset_1(D_100, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_198])).
% 8.27/2.86  tff(c_1743, plain, (r2_lattice3('#skF_3', '#skF_4', '#skF_7')), inference(splitRight, [status(thm)], [c_74])).
% 8.27/2.86  tff(c_1792, plain, (![A_493, B_494, D_495, C_496]: (r2_lattice3(A_493, B_494, D_495) | ~r2_lattice3(A_493, C_496, D_495) | ~m1_subset_1(D_495, u1_struct_0(A_493)) | ~r1_tarski(B_494, C_496) | ~l1_orders_2(A_493))), inference(cnfTransformation, [status(thm)], [f_139])).
% 8.27/2.86  tff(c_1794, plain, (![B_494]: (r2_lattice3('#skF_3', B_494, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~r1_tarski(B_494, '#skF_4') | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_1743, c_1792])).
% 8.27/2.86  tff(c_1797, plain, (![B_494]: (r2_lattice3('#skF_3', B_494, '#skF_7') | ~r1_tarski(B_494, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_1794])).
% 8.27/2.86  tff(c_1832, plain, (![A_502, B_503, C_504]: (m1_subset_1('#skF_1'(A_502, B_503, C_504), u1_struct_0(A_502)) | r2_lattice3(A_502, B_503, C_504) | ~m1_subset_1(C_504, u1_struct_0(A_502)) | ~l1_orders_2(A_502))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.27/2.86  tff(c_76, plain, (![D_100]: (k1_yellow_0('#skF_3', '#skF_6'(D_100))=D_100 | ~r2_hidden(D_100, '#skF_5') | ~m1_subset_1(D_100, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_198])).
% 8.27/2.86  tff(c_1836, plain, (![B_503, C_504]: (k1_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_503, C_504)))='#skF_1'('#skF_3', B_503, C_504) | ~r2_hidden('#skF_1'('#skF_3', B_503, C_504), '#skF_5') | r2_lattice3('#skF_3', B_503, C_504) | ~m1_subset_1(C_504, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_1832, c_76])).
% 8.27/2.86  tff(c_1843, plain, (![B_503, C_504]: (k1_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_503, C_504)))='#skF_1'('#skF_3', B_503, C_504) | ~r2_hidden('#skF_1'('#skF_3', B_503, C_504), '#skF_5') | r2_lattice3('#skF_3', B_503, C_504) | ~m1_subset_1(C_504, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1836])).
% 8.27/2.86  tff(c_2177, plain, (![B_614, C_615]: (k1_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_614, C_615)))='#skF_1'('#skF_3', B_614, C_615) | ~r2_hidden('#skF_1'('#skF_3', B_614, C_615), '#skF_5') | r2_lattice3('#skF_3', B_614, C_615) | ~m1_subset_1(C_615, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1836])).
% 8.27/2.86  tff(c_34, plain, (![A_25, B_32, D_36]: (r1_orders_2(A_25, k1_yellow_0(A_25, B_32), D_36) | ~r2_lattice3(A_25, B_32, D_36) | ~m1_subset_1(D_36, u1_struct_0(A_25)) | ~r1_yellow_0(A_25, B_32) | ~m1_subset_1(k1_yellow_0(A_25, B_32), u1_struct_0(A_25)) | ~l1_orders_2(A_25))), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.27/2.86  tff(c_2182, plain, (![B_614, C_615, D_36]: (r1_orders_2('#skF_3', k1_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_614, C_615))), D_36) | ~r2_lattice3('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_614, C_615)), D_36) | ~m1_subset_1(D_36, u1_struct_0('#skF_3')) | ~r1_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_614, C_615))) | ~m1_subset_1('#skF_1'('#skF_3', B_614, C_615), u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~r2_hidden('#skF_1'('#skF_3', B_614, C_615), '#skF_5') | r2_lattice3('#skF_3', B_614, C_615) | ~m1_subset_1(C_615, u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2177, c_34])).
% 8.27/2.86  tff(c_3595, plain, (![B_946, C_947, D_948]: (r1_orders_2('#skF_3', k1_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_946, C_947))), D_948) | ~r2_lattice3('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_946, C_947)), D_948) | ~m1_subset_1(D_948, u1_struct_0('#skF_3')) | ~r1_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_946, C_947))) | ~m1_subset_1('#skF_1'('#skF_3', B_946, C_947), u1_struct_0('#skF_3')) | ~r2_hidden('#skF_1'('#skF_3', B_946, C_947), '#skF_5') | r2_lattice3('#skF_3', B_946, C_947) | ~m1_subset_1(C_947, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2182])).
% 8.27/2.86  tff(c_4916, plain, (![B_1322, C_1323, D_1324]: (r1_orders_2('#skF_3', '#skF_1'('#skF_3', B_1322, C_1323), D_1324) | ~r2_lattice3('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_1322, C_1323)), D_1324) | ~m1_subset_1(D_1324, u1_struct_0('#skF_3')) | ~r1_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_1322, C_1323))) | ~m1_subset_1('#skF_1'('#skF_3', B_1322, C_1323), u1_struct_0('#skF_3')) | ~r2_hidden('#skF_1'('#skF_3', B_1322, C_1323), '#skF_5') | r2_lattice3('#skF_3', B_1322, C_1323) | ~m1_subset_1(C_1323, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_1'('#skF_3', B_1322, C_1323), '#skF_5') | r2_lattice3('#skF_3', B_1322, C_1323) | ~m1_subset_1(C_1323, u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1843, c_3595])).
% 8.27/2.86  tff(c_4958, plain, (![B_1322, C_1323]: (r1_orders_2('#skF_3', '#skF_1'('#skF_3', B_1322, C_1323), '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~r1_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_1322, C_1323))) | ~m1_subset_1('#skF_1'('#skF_3', B_1322, C_1323), u1_struct_0('#skF_3')) | ~r2_hidden('#skF_1'('#skF_3', B_1322, C_1323), '#skF_5') | r2_lattice3('#skF_3', B_1322, C_1323) | ~m1_subset_1(C_1323, u1_struct_0('#skF_3')) | ~r1_tarski('#skF_6'('#skF_1'('#skF_3', B_1322, C_1323)), '#skF_4'))), inference(resolution, [status(thm)], [c_1797, c_4916])).
% 8.27/2.86  tff(c_4988, plain, (![B_1325, C_1326]: (r1_orders_2('#skF_3', '#skF_1'('#skF_3', B_1325, C_1326), '#skF_7') | ~r1_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_1325, C_1326))) | ~m1_subset_1('#skF_1'('#skF_3', B_1325, C_1326), u1_struct_0('#skF_3')) | ~r2_hidden('#skF_1'('#skF_3', B_1325, C_1326), '#skF_5') | r2_lattice3('#skF_3', B_1325, C_1326) | ~m1_subset_1(C_1326, u1_struct_0('#skF_3')) | ~r1_tarski('#skF_6'('#skF_1'('#skF_3', B_1325, C_1326)), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_4958])).
% 8.27/2.86  tff(c_4997, plain, (![B_1327, C_1328]: (r1_orders_2('#skF_3', '#skF_1'('#skF_3', B_1327, C_1328), '#skF_7') | r2_lattice3('#skF_3', B_1327, C_1328) | ~m1_subset_1(C_1328, u1_struct_0('#skF_3')) | ~r1_tarski('#skF_6'('#skF_1'('#skF_3', B_1327, C_1328)), '#skF_4') | ~r2_hidden('#skF_1'('#skF_3', B_1327, C_1328), '#skF_5') | ~m1_subset_1('#skF_1'('#skF_3', B_1327, C_1328), u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_78, c_4988])).
% 8.27/2.86  tff(c_5002, plain, (![B_1329, C_1330]: (r1_orders_2('#skF_3', '#skF_1'('#skF_3', B_1329, C_1330), '#skF_7') | r2_lattice3('#skF_3', B_1329, C_1330) | ~m1_subset_1(C_1330, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_1'('#skF_3', B_1329, C_1330), '#skF_5') | ~m1_subset_1('#skF_1'('#skF_3', B_1329, C_1330), u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_1788, c_4997])).
% 8.27/2.86  tff(c_5006, plain, (![B_20, C_21]: (r1_orders_2('#skF_3', '#skF_1'('#skF_3', B_20, C_21), '#skF_7') | ~r2_hidden('#skF_1'('#skF_3', B_20, C_21), '#skF_5') | r2_lattice3('#skF_3', B_20, C_21) | ~m1_subset_1(C_21, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_26, c_5002])).
% 8.27/2.86  tff(c_5010, plain, (![B_1331, C_1332]: (r1_orders_2('#skF_3', '#skF_1'('#skF_3', B_1331, C_1332), '#skF_7') | ~r2_hidden('#skF_1'('#skF_3', B_1331, C_1332), '#skF_5') | r2_lattice3('#skF_3', B_1331, C_1332) | ~m1_subset_1(C_1332, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_5006])).
% 8.27/2.86  tff(c_5018, plain, (![B_1331]: (~l1_orders_2('#skF_3') | ~r2_hidden('#skF_1'('#skF_3', B_1331, '#skF_7'), '#skF_5') | r2_lattice3('#skF_3', B_1331, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_5010, c_22])).
% 8.27/2.86  tff(c_5028, plain, (![B_1333]: (~r2_hidden('#skF_1'('#skF_3', B_1333, '#skF_7'), '#skF_5') | r2_lattice3('#skF_3', B_1333, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_60, c_5018])).
% 8.27/2.86  tff(c_5036, plain, (r2_lattice3('#skF_3', '#skF_5', '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_24, c_5028])).
% 8.27/2.86  tff(c_5042, plain, (r2_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_5036])).
% 8.27/2.86  tff(c_5044, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1744, c_5042])).
% 8.27/2.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.27/2.86  
% 8.27/2.86  Inference rules
% 8.27/2.86  ----------------------
% 8.27/2.86  #Ref     : 0
% 8.27/2.86  #Sup     : 971
% 8.27/2.86  #Fact    : 0
% 8.27/2.86  #Define  : 0
% 8.27/2.86  #Split   : 15
% 8.27/2.86  #Chain   : 0
% 8.27/2.86  #Close   : 0
% 8.27/2.86  
% 8.27/2.86  Ordering : KBO
% 8.27/2.86  
% 8.27/2.86  Simplification rules
% 8.27/2.86  ----------------------
% 8.27/2.86  #Subsume      : 244
% 8.27/2.86  #Demod        : 647
% 8.27/2.86  #Tautology    : 52
% 8.27/2.86  #SimpNegUnit  : 92
% 8.27/2.86  #BackRed      : 0
% 8.27/2.86  
% 8.27/2.86  #Partial instantiations: 0
% 8.27/2.86  #Strategies tried      : 1
% 8.27/2.86  
% 8.27/2.86  Timing (in seconds)
% 8.27/2.86  ----------------------
% 8.27/2.86  Preprocessing        : 0.34
% 8.27/2.86  Parsing              : 0.18
% 8.27/2.86  CNF conversion       : 0.03
% 8.27/2.86  Main loop            : 1.75
% 8.27/2.86  Inferencing          : 0.66
% 8.27/2.86  Reduction            : 0.47
% 8.27/2.86  Demodulation         : 0.30
% 8.27/2.86  BG Simplification    : 0.06
% 8.27/2.86  Subsumption          : 0.45
% 8.27/2.86  Abstraction          : 0.07
% 8.27/2.86  MUC search           : 0.00
% 8.27/2.86  Cooper               : 0.00
% 8.27/2.86  Total                : 2.14
% 8.27/2.86  Index Insertion      : 0.00
% 8.27/2.86  Index Deletion       : 0.00
% 8.27/2.86  Index Matching       : 0.00
% 8.27/2.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
