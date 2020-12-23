%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:01 EST 2020

% Result     : Theorem 8.48s
% Output     : CNFRefutation 8.75s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 240 expanded)
%              Number of leaves         :   41 ( 102 expanded)
%              Depth                    :   24
%              Number of atoms          :  457 (1589 expanded)
%              Number of equality atoms :   40 ( 168 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_waybel_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_39,axiom,(
    ! [A] : v1_finset_1(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_finset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => r3_orders_2(A,B,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_yellow_0)).

tff(f_29,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_70,plain,
    ( ~ r2_lattice3('#skF_3','#skF_5','#skF_7')
    | ~ r2_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_107,plain,(
    ~ r2_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_62,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_52,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_26,plain,(
    ! [A_13,B_20,C_21] :
      ( r2_hidden('#skF_1'(A_13,B_20,C_21),B_20)
      | r2_lattice3(A_13,B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0(A_13))
      | ~ l1_orders_2(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_8,plain,(
    ! [A_2,B_3] :
      ( r1_tarski(k1_tarski(A_2),B_3)
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_6] : v1_finset_1(k1_tarski(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_28,plain,(
    ! [A_13,B_20,C_21] :
      ( m1_subset_1('#skF_1'(A_13,B_20,C_21),u1_struct_0(A_13))
      | r2_lattice3(A_13,B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0(A_13))
      | ~ l1_orders_2(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_66,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_198,plain,(
    ! [A_145,B_146,C_147] :
      ( r3_orders_2(A_145,B_146,B_146)
      | ~ m1_subset_1(C_147,u1_struct_0(A_145))
      | ~ m1_subset_1(B_146,u1_struct_0(A_145))
      | ~ l1_orders_2(A_145)
      | ~ v3_orders_2(A_145)
      | v2_struct_0(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_202,plain,(
    ! [B_146] :
      ( r3_orders_2('#skF_3',B_146,B_146)
      | ~ m1_subset_1(B_146,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_52,c_198])).

tff(c_206,plain,(
    ! [B_146] :
      ( r3_orders_2('#skF_3',B_146,B_146)
      | ~ m1_subset_1(B_146,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_202])).

tff(c_208,plain,(
    ! [B_148] :
      ( r3_orders_2('#skF_3',B_148,B_148)
      | ~ m1_subset_1(B_148,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_206])).

tff(c_211,plain,(
    ! [B_20,C_21] :
      ( r3_orders_2('#skF_3','#skF_1'('#skF_3',B_20,C_21),'#skF_1'('#skF_3',B_20,C_21))
      | r2_lattice3('#skF_3',B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_28,c_208])).

tff(c_216,plain,(
    ! [B_20,C_21] :
      ( r3_orders_2('#skF_3','#skF_1'('#skF_3',B_20,C_21),'#skF_1'('#skF_3',B_20,C_21))
      | r2_lattice3('#skF_3',B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_211])).

tff(c_322,plain,(
    ! [A_184,B_185,C_186] :
      ( r1_orders_2(A_184,B_185,C_186)
      | ~ r3_orders_2(A_184,B_185,C_186)
      | ~ m1_subset_1(C_186,u1_struct_0(A_184))
      | ~ m1_subset_1(B_185,u1_struct_0(A_184))
      | ~ l1_orders_2(A_184)
      | ~ v3_orders_2(A_184)
      | v2_struct_0(A_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_324,plain,(
    ! [B_20,C_21] :
      ( r1_orders_2('#skF_3','#skF_1'('#skF_3',B_20,C_21),'#skF_1'('#skF_3',B_20,C_21))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_20,C_21),u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3')
      | r2_lattice3('#skF_3',B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_216,c_322])).

tff(c_329,plain,(
    ! [B_20,C_21] :
      ( r1_orders_2('#skF_3','#skF_1'('#skF_3',B_20,C_21),'#skF_1'('#skF_3',B_20,C_21))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_20,C_21),u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3')
      | r2_lattice3('#skF_3',B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_324])).

tff(c_330,plain,(
    ! [B_20,C_21] :
      ( r1_orders_2('#skF_3','#skF_1'('#skF_3',B_20,C_21),'#skF_1'('#skF_3',B_20,C_21))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_20,C_21),u1_struct_0('#skF_3'))
      | r2_lattice3('#skF_3',B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_329])).

tff(c_116,plain,(
    ! [D_115] :
      ( r1_yellow_0('#skF_3',D_115)
      | k1_xboole_0 = D_115
      | ~ m1_subset_1(D_115,k1_zfmisc_1('#skF_4'))
      | ~ v1_finset_1(D_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_121,plain,(
    ! [A_4] :
      ( r1_yellow_0('#skF_3',A_4)
      | k1_xboole_0 = A_4
      | ~ v1_finset_1(A_4)
      | ~ r1_tarski(A_4,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_12,c_116])).

tff(c_40,plain,(
    ! [A_37,C_43,B_41] :
      ( r2_lattice3(A_37,k1_tarski(C_43),B_41)
      | ~ r1_orders_2(A_37,C_43,B_41)
      | ~ m1_subset_1(C_43,u1_struct_0(A_37))
      | ~ m1_subset_1(B_41,u1_struct_0(A_37))
      | ~ l1_orders_2(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_34,plain,(
    ! [A_25,B_32,C_33] :
      ( m1_subset_1('#skF_2'(A_25,B_32,C_33),u1_struct_0(A_25))
      | k1_yellow_0(A_25,B_32) = C_33
      | ~ r2_lattice3(A_25,B_32,C_33)
      | ~ r1_yellow_0(A_25,B_32)
      | ~ m1_subset_1(C_33,u1_struct_0(A_25))
      | ~ l1_orders_2(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_355,plain,(
    ! [A_199,B_200,C_201] :
      ( r2_lattice3(A_199,B_200,'#skF_2'(A_199,B_200,C_201))
      | k1_yellow_0(A_199,B_200) = C_201
      | ~ r2_lattice3(A_199,B_200,C_201)
      | ~ r1_yellow_0(A_199,B_200)
      | ~ m1_subset_1(C_201,u1_struct_0(A_199))
      | ~ l1_orders_2(A_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_42,plain,(
    ! [A_37,C_43,B_41] :
      ( r1_orders_2(A_37,C_43,B_41)
      | ~ r2_lattice3(A_37,k1_tarski(C_43),B_41)
      | ~ m1_subset_1(C_43,u1_struct_0(A_37))
      | ~ m1_subset_1(B_41,u1_struct_0(A_37))
      | ~ l1_orders_2(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1114,plain,(
    ! [A_412,C_413,C_414] :
      ( r1_orders_2(A_412,C_413,'#skF_2'(A_412,k1_tarski(C_413),C_414))
      | ~ m1_subset_1(C_413,u1_struct_0(A_412))
      | ~ m1_subset_1('#skF_2'(A_412,k1_tarski(C_413),C_414),u1_struct_0(A_412))
      | k1_yellow_0(A_412,k1_tarski(C_413)) = C_414
      | ~ r2_lattice3(A_412,k1_tarski(C_413),C_414)
      | ~ r1_yellow_0(A_412,k1_tarski(C_413))
      | ~ m1_subset_1(C_414,u1_struct_0(A_412))
      | ~ l1_orders_2(A_412) ) ),
    inference(resolution,[status(thm)],[c_355,c_42])).

tff(c_1119,plain,(
    ! [A_415,C_416,C_417] :
      ( r1_orders_2(A_415,C_416,'#skF_2'(A_415,k1_tarski(C_416),C_417))
      | ~ m1_subset_1(C_416,u1_struct_0(A_415))
      | k1_yellow_0(A_415,k1_tarski(C_416)) = C_417
      | ~ r2_lattice3(A_415,k1_tarski(C_416),C_417)
      | ~ r1_yellow_0(A_415,k1_tarski(C_416))
      | ~ m1_subset_1(C_417,u1_struct_0(A_415))
      | ~ l1_orders_2(A_415) ) ),
    inference(resolution,[status(thm)],[c_34,c_1114])).

tff(c_30,plain,(
    ! [A_25,C_33,B_32] :
      ( ~ r1_orders_2(A_25,C_33,'#skF_2'(A_25,B_32,C_33))
      | k1_yellow_0(A_25,B_32) = C_33
      | ~ r2_lattice3(A_25,B_32,C_33)
      | ~ r1_yellow_0(A_25,B_32)
      | ~ m1_subset_1(C_33,u1_struct_0(A_25))
      | ~ l1_orders_2(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1131,plain,(
    ! [A_418,C_419] :
      ( k1_yellow_0(A_418,k1_tarski(C_419)) = C_419
      | ~ r2_lattice3(A_418,k1_tarski(C_419),C_419)
      | ~ r1_yellow_0(A_418,k1_tarski(C_419))
      | ~ m1_subset_1(C_419,u1_struct_0(A_418))
      | ~ l1_orders_2(A_418) ) ),
    inference(resolution,[status(thm)],[c_1119,c_30])).

tff(c_1306,plain,(
    ! [A_436,B_437] :
      ( k1_yellow_0(A_436,k1_tarski(B_437)) = B_437
      | ~ r1_yellow_0(A_436,k1_tarski(B_437))
      | ~ r1_orders_2(A_436,B_437,B_437)
      | ~ m1_subset_1(B_437,u1_struct_0(A_436))
      | ~ l1_orders_2(A_436) ) ),
    inference(resolution,[status(thm)],[c_40,c_1131])).

tff(c_1309,plain,(
    ! [B_437] :
      ( k1_yellow_0('#skF_3',k1_tarski(B_437)) = B_437
      | ~ r1_orders_2('#skF_3',B_437,B_437)
      | ~ m1_subset_1(B_437,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | k1_tarski(B_437) = k1_xboole_0
      | ~ v1_finset_1(k1_tarski(B_437))
      | ~ r1_tarski(k1_tarski(B_437),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_121,c_1306])).

tff(c_1313,plain,(
    ! [B_438] :
      ( k1_yellow_0('#skF_3',k1_tarski(B_438)) = B_438
      | ~ r1_orders_2('#skF_3',B_438,B_438)
      | ~ m1_subset_1(B_438,u1_struct_0('#skF_3'))
      | k1_tarski(B_438) = k1_xboole_0
      | ~ r1_tarski(k1_tarski(B_438),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_62,c_1309])).

tff(c_1432,plain,(
    ! [B_460,C_461] :
      ( k1_yellow_0('#skF_3',k1_tarski('#skF_1'('#skF_3',B_460,C_461))) = '#skF_1'('#skF_3',B_460,C_461)
      | k1_tarski('#skF_1'('#skF_3',B_460,C_461)) = k1_xboole_0
      | ~ r1_tarski(k1_tarski('#skF_1'('#skF_3',B_460,C_461)),'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_3',B_460,C_461),u1_struct_0('#skF_3'))
      | r2_lattice3('#skF_3',B_460,C_461)
      | ~ m1_subset_1(C_461,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_330,c_1313])).

tff(c_1899,plain,(
    ! [B_588,C_589] :
      ( k1_yellow_0('#skF_3',k1_tarski('#skF_1'('#skF_3',B_588,C_589))) = '#skF_1'('#skF_3',B_588,C_589)
      | k1_tarski('#skF_1'('#skF_3',B_588,C_589)) = k1_xboole_0
      | ~ m1_subset_1('#skF_1'('#skF_3',B_588,C_589),u1_struct_0('#skF_3'))
      | r2_lattice3('#skF_3',B_588,C_589)
      | ~ m1_subset_1(C_589,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'('#skF_3',B_588,C_589),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_8,c_1432])).

tff(c_1903,plain,(
    ! [B_20,C_21] :
      ( k1_yellow_0('#skF_3',k1_tarski('#skF_1'('#skF_3',B_20,C_21))) = '#skF_1'('#skF_3',B_20,C_21)
      | k1_tarski('#skF_1'('#skF_3',B_20,C_21)) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_20,C_21),'#skF_4')
      | r2_lattice3('#skF_3',B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_28,c_1899])).

tff(c_1907,plain,(
    ! [B_590,C_591] :
      ( k1_yellow_0('#skF_3',k1_tarski('#skF_1'('#skF_3',B_590,C_591))) = '#skF_1'('#skF_3',B_590,C_591)
      | k1_tarski('#skF_1'('#skF_3',B_590,C_591)) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_590,C_591),'#skF_4')
      | r2_lattice3('#skF_3',B_590,C_591)
      | ~ m1_subset_1(C_591,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1903])).

tff(c_54,plain,(
    ! [D_102] :
      ( r2_hidden(k1_yellow_0('#skF_3',D_102),'#skF_5')
      | k1_xboole_0 = D_102
      | ~ m1_subset_1(D_102,k1_zfmisc_1('#skF_4'))
      | ~ v1_finset_1(D_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_1919,plain,(
    ! [B_590,C_591] :
      ( r2_hidden('#skF_1'('#skF_3',B_590,C_591),'#skF_5')
      | k1_tarski('#skF_1'('#skF_3',B_590,C_591)) = k1_xboole_0
      | ~ m1_subset_1(k1_tarski('#skF_1'('#skF_3',B_590,C_591)),k1_zfmisc_1('#skF_4'))
      | ~ v1_finset_1(k1_tarski('#skF_1'('#skF_3',B_590,C_591)))
      | k1_tarski('#skF_1'('#skF_3',B_590,C_591)) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_590,C_591),'#skF_4')
      | r2_lattice3('#skF_3',B_590,C_591)
      | ~ m1_subset_1(C_591,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1907,c_54])).

tff(c_1933,plain,(
    ! [B_592,C_593] :
      ( r2_hidden('#skF_1'('#skF_3',B_592,C_593),'#skF_5')
      | ~ m1_subset_1(k1_tarski('#skF_1'('#skF_3',B_592,C_593)),k1_zfmisc_1('#skF_4'))
      | k1_tarski('#skF_1'('#skF_3',B_592,C_593)) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_592,C_593),'#skF_4')
      | r2_lattice3('#skF_3',B_592,C_593)
      | ~ m1_subset_1(C_593,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1919])).

tff(c_1938,plain,(
    ! [B_594,C_595] :
      ( r2_hidden('#skF_1'('#skF_3',B_594,C_595),'#skF_5')
      | k1_tarski('#skF_1'('#skF_3',B_594,C_595)) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_594,C_595),'#skF_4')
      | r2_lattice3('#skF_3',B_594,C_595)
      | ~ m1_subset_1(C_595,u1_struct_0('#skF_3'))
      | ~ r1_tarski(k1_tarski('#skF_1'('#skF_3',B_594,C_595)),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_12,c_1933])).

tff(c_1943,plain,(
    ! [B_596,C_597] :
      ( r2_hidden('#skF_1'('#skF_3',B_596,C_597),'#skF_5')
      | k1_tarski('#skF_1'('#skF_3',B_596,C_597)) = k1_xboole_0
      | r2_lattice3('#skF_3',B_596,C_597)
      | ~ m1_subset_1(C_597,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'('#skF_3',B_596,C_597),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_8,c_1938])).

tff(c_76,plain,
    ( r2_lattice3('#skF_3','#skF_4','#skF_7')
    | r2_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_108,plain,(
    r2_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_76])).

tff(c_140,plain,(
    ! [A_124,B_125,D_126,C_127] :
      ( r2_lattice3(A_124,B_125,D_126)
      | ~ r2_lattice3(A_124,C_127,D_126)
      | ~ m1_subset_1(D_126,u1_struct_0(A_124))
      | ~ r1_tarski(B_125,C_127)
      | ~ l1_orders_2(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_142,plain,(
    ! [B_125] :
      ( r2_lattice3('#skF_3',B_125,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ r1_tarski(B_125,'#skF_5')
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_108,c_140])).

tff(c_145,plain,(
    ! [B_125] :
      ( r2_lattice3('#skF_3',B_125,'#skF_7')
      | ~ r1_tarski(B_125,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_142])).

tff(c_228,plain,(
    ! [A_157,C_158,B_159] :
      ( r1_orders_2(A_157,C_158,B_159)
      | ~ r2_lattice3(A_157,k1_tarski(C_158),B_159)
      | ~ m1_subset_1(C_158,u1_struct_0(A_157))
      | ~ m1_subset_1(B_159,u1_struct_0(A_157))
      | ~ l1_orders_2(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_232,plain,(
    ! [C_158] :
      ( r1_orders_2('#skF_3',C_158,'#skF_7')
      | ~ m1_subset_1(C_158,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ r1_tarski(k1_tarski(C_158),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_145,c_228])).

tff(c_237,plain,(
    ! [C_162] :
      ( r1_orders_2('#skF_3',C_162,'#skF_7')
      | ~ m1_subset_1(C_162,u1_struct_0('#skF_3'))
      | ~ r1_tarski(k1_tarski(C_162),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_232])).

tff(c_243,plain,(
    ! [A_163] :
      ( r1_orders_2('#skF_3',A_163,'#skF_7')
      | ~ m1_subset_1(A_163,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_163,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_8,c_237])).

tff(c_247,plain,(
    ! [B_20,C_21] :
      ( r1_orders_2('#skF_3','#skF_1'('#skF_3',B_20,C_21),'#skF_7')
      | ~ r2_hidden('#skF_1'('#skF_3',B_20,C_21),'#skF_5')
      | r2_lattice3('#skF_3',B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_28,c_243])).

tff(c_305,plain,(
    ! [B_178,C_179] :
      ( r1_orders_2('#skF_3','#skF_1'('#skF_3',B_178,C_179),'#skF_7')
      | ~ r2_hidden('#skF_1'('#skF_3',B_178,C_179),'#skF_5')
      | r2_lattice3('#skF_3',B_178,C_179)
      | ~ m1_subset_1(C_179,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_247])).

tff(c_24,plain,(
    ! [A_13,B_20,C_21] :
      ( ~ r1_orders_2(A_13,'#skF_1'(A_13,B_20,C_21),C_21)
      | r2_lattice3(A_13,B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0(A_13))
      | ~ l1_orders_2(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_309,plain,(
    ! [B_178] :
      ( ~ l1_orders_2('#skF_3')
      | ~ r2_hidden('#skF_1'('#skF_3',B_178,'#skF_7'),'#skF_5')
      | r2_lattice3('#skF_3',B_178,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_305,c_24])).

tff(c_312,plain,(
    ! [B_178] :
      ( ~ r2_hidden('#skF_1'('#skF_3',B_178,'#skF_7'),'#skF_5')
      | r2_lattice3('#skF_3',B_178,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_62,c_309])).

tff(c_1952,plain,(
    ! [B_596] :
      ( k1_tarski('#skF_1'('#skF_3',B_596,'#skF_7')) = k1_xboole_0
      | r2_lattice3('#skF_3',B_596,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'('#skF_3',B_596,'#skF_7'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1943,c_312])).

tff(c_1964,plain,(
    ! [B_598] :
      ( k1_tarski('#skF_1'('#skF_3',B_598,'#skF_7')) = k1_xboole_0
      | r2_lattice3('#skF_3',B_598,'#skF_7')
      | ~ r2_hidden('#skF_1'('#skF_3',B_598,'#skF_7'),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1952])).

tff(c_1968,plain,
    ( k1_tarski('#skF_1'('#skF_3','#skF_4','#skF_7')) = k1_xboole_0
    | r2_lattice3('#skF_3','#skF_4','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_1964])).

tff(c_1971,plain,
    ( k1_tarski('#skF_1'('#skF_3','#skF_4','#skF_7')) = k1_xboole_0
    | r2_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_1968])).

tff(c_1972,plain,(
    k1_tarski('#skF_1'('#skF_3','#skF_4','#skF_7')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_1971])).

tff(c_4,plain,(
    ! [A_1] : ~ v1_xboole_0(k1_tarski(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2107,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1972,c_4])).

tff(c_2156,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2107])).

tff(c_2157,plain,(
    ~ r2_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_2175,plain,(
    ! [D_603] :
      ( m1_subset_1('#skF_6'(D_603),k1_zfmisc_1('#skF_4'))
      | ~ r2_hidden(D_603,'#skF_5')
      | ~ m1_subset_1(D_603,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2183,plain,(
    ! [D_603] :
      ( r1_tarski('#skF_6'(D_603),'#skF_4')
      | ~ r2_hidden(D_603,'#skF_5')
      | ~ m1_subset_1(D_603,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_2175,c_10])).

tff(c_80,plain,(
    ! [D_100] :
      ( r1_yellow_0('#skF_3','#skF_6'(D_100))
      | ~ r2_hidden(D_100,'#skF_5')
      | ~ m1_subset_1(D_100,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_2158,plain,(
    r2_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_2192,plain,(
    ! [A_610,B_611,D_612,C_613] :
      ( r2_lattice3(A_610,B_611,D_612)
      | ~ r2_lattice3(A_610,C_613,D_612)
      | ~ m1_subset_1(D_612,u1_struct_0(A_610))
      | ~ r1_tarski(B_611,C_613)
      | ~ l1_orders_2(A_610) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2194,plain,(
    ! [B_611] :
      ( r2_lattice3('#skF_3',B_611,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ r1_tarski(B_611,'#skF_4')
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2158,c_2192])).

tff(c_2197,plain,(
    ! [B_611] :
      ( r2_lattice3('#skF_3',B_611,'#skF_7')
      | ~ r1_tarski(B_611,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_2194])).

tff(c_2234,plain,(
    ! [A_626,B_627,C_628] :
      ( m1_subset_1('#skF_1'(A_626,B_627,C_628),u1_struct_0(A_626))
      | r2_lattice3(A_626,B_627,C_628)
      | ~ m1_subset_1(C_628,u1_struct_0(A_626))
      | ~ l1_orders_2(A_626) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_78,plain,(
    ! [D_100] :
      ( k1_yellow_0('#skF_3','#skF_6'(D_100)) = D_100
      | ~ r2_hidden(D_100,'#skF_5')
      | ~ m1_subset_1(D_100,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_2238,plain,(
    ! [B_627,C_628] :
      ( k1_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_627,C_628))) = '#skF_1'('#skF_3',B_627,C_628)
      | ~ r2_hidden('#skF_1'('#skF_3',B_627,C_628),'#skF_5')
      | r2_lattice3('#skF_3',B_627,C_628)
      | ~ m1_subset_1(C_628,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2234,c_78])).

tff(c_2245,plain,(
    ! [B_627,C_628] :
      ( k1_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_627,C_628))) = '#skF_1'('#skF_3',B_627,C_628)
      | ~ r2_hidden('#skF_1'('#skF_3',B_627,C_628),'#skF_5')
      | r2_lattice3('#skF_3',B_627,C_628)
      | ~ m1_subset_1(C_628,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2238])).

tff(c_2578,plain,(
    ! [B_731,C_732] :
      ( k1_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_731,C_732))) = '#skF_1'('#skF_3',B_731,C_732)
      | ~ r2_hidden('#skF_1'('#skF_3',B_731,C_732),'#skF_5')
      | r2_lattice3('#skF_3',B_731,C_732)
      | ~ m1_subset_1(C_732,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2238])).

tff(c_36,plain,(
    ! [A_25,B_32,D_36] :
      ( r1_orders_2(A_25,k1_yellow_0(A_25,B_32),D_36)
      | ~ r2_lattice3(A_25,B_32,D_36)
      | ~ m1_subset_1(D_36,u1_struct_0(A_25))
      | ~ r1_yellow_0(A_25,B_32)
      | ~ m1_subset_1(k1_yellow_0(A_25,B_32),u1_struct_0(A_25))
      | ~ l1_orders_2(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2583,plain,(
    ! [B_731,C_732,D_36] :
      ( r1_orders_2('#skF_3',k1_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_731,C_732))),D_36)
      | ~ r2_lattice3('#skF_3','#skF_6'('#skF_1'('#skF_3',B_731,C_732)),D_36)
      | ~ m1_subset_1(D_36,u1_struct_0('#skF_3'))
      | ~ r1_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_731,C_732)))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_731,C_732),u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ r2_hidden('#skF_1'('#skF_3',B_731,C_732),'#skF_5')
      | r2_lattice3('#skF_3',B_731,C_732)
      | ~ m1_subset_1(C_732,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2578,c_36])).

tff(c_3964,plain,(
    ! [B_1072,C_1073,D_1074] :
      ( r1_orders_2('#skF_3',k1_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_1072,C_1073))),D_1074)
      | ~ r2_lattice3('#skF_3','#skF_6'('#skF_1'('#skF_3',B_1072,C_1073)),D_1074)
      | ~ m1_subset_1(D_1074,u1_struct_0('#skF_3'))
      | ~ r1_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_1072,C_1073)))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_1072,C_1073),u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'('#skF_3',B_1072,C_1073),'#skF_5')
      | r2_lattice3('#skF_3',B_1072,C_1073)
      | ~ m1_subset_1(C_1073,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2583])).

tff(c_5325,plain,(
    ! [B_1472,C_1473,D_1474] :
      ( r1_orders_2('#skF_3','#skF_1'('#skF_3',B_1472,C_1473),D_1474)
      | ~ r2_lattice3('#skF_3','#skF_6'('#skF_1'('#skF_3',B_1472,C_1473)),D_1474)
      | ~ m1_subset_1(D_1474,u1_struct_0('#skF_3'))
      | ~ r1_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_1472,C_1473)))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_1472,C_1473),u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'('#skF_3',B_1472,C_1473),'#skF_5')
      | r2_lattice3('#skF_3',B_1472,C_1473)
      | ~ m1_subset_1(C_1473,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'('#skF_3',B_1472,C_1473),'#skF_5')
      | r2_lattice3('#skF_3',B_1472,C_1473)
      | ~ m1_subset_1(C_1473,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2245,c_3964])).

tff(c_5367,plain,(
    ! [B_1472,C_1473] :
      ( r1_orders_2('#skF_3','#skF_1'('#skF_3',B_1472,C_1473),'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ r1_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_1472,C_1473)))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_1472,C_1473),u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'('#skF_3',B_1472,C_1473),'#skF_5')
      | r2_lattice3('#skF_3',B_1472,C_1473)
      | ~ m1_subset_1(C_1473,u1_struct_0('#skF_3'))
      | ~ r1_tarski('#skF_6'('#skF_1'('#skF_3',B_1472,C_1473)),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2197,c_5325])).

tff(c_5402,plain,(
    ! [B_1480,C_1481] :
      ( r1_orders_2('#skF_3','#skF_1'('#skF_3',B_1480,C_1481),'#skF_7')
      | ~ r1_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_1480,C_1481)))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_1480,C_1481),u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'('#skF_3',B_1480,C_1481),'#skF_5')
      | r2_lattice3('#skF_3',B_1480,C_1481)
      | ~ m1_subset_1(C_1481,u1_struct_0('#skF_3'))
      | ~ r1_tarski('#skF_6'('#skF_1'('#skF_3',B_1480,C_1481)),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_5367])).

tff(c_5411,plain,(
    ! [B_1482,C_1483] :
      ( r1_orders_2('#skF_3','#skF_1'('#skF_3',B_1482,C_1483),'#skF_7')
      | r2_lattice3('#skF_3',B_1482,C_1483)
      | ~ m1_subset_1(C_1483,u1_struct_0('#skF_3'))
      | ~ r1_tarski('#skF_6'('#skF_1'('#skF_3',B_1482,C_1483)),'#skF_4')
      | ~ r2_hidden('#skF_1'('#skF_3',B_1482,C_1483),'#skF_5')
      | ~ m1_subset_1('#skF_1'('#skF_3',B_1482,C_1483),u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_80,c_5402])).

tff(c_5416,plain,(
    ! [B_1484,C_1485] :
      ( r1_orders_2('#skF_3','#skF_1'('#skF_3',B_1484,C_1485),'#skF_7')
      | r2_lattice3('#skF_3',B_1484,C_1485)
      | ~ m1_subset_1(C_1485,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'('#skF_3',B_1484,C_1485),'#skF_5')
      | ~ m1_subset_1('#skF_1'('#skF_3',B_1484,C_1485),u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_2183,c_5411])).

tff(c_5420,plain,(
    ! [B_20,C_21] :
      ( r1_orders_2('#skF_3','#skF_1'('#skF_3',B_20,C_21),'#skF_7')
      | ~ r2_hidden('#skF_1'('#skF_3',B_20,C_21),'#skF_5')
      | r2_lattice3('#skF_3',B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_28,c_5416])).

tff(c_5424,plain,(
    ! [B_1486,C_1487] :
      ( r1_orders_2('#skF_3','#skF_1'('#skF_3',B_1486,C_1487),'#skF_7')
      | ~ r2_hidden('#skF_1'('#skF_3',B_1486,C_1487),'#skF_5')
      | r2_lattice3('#skF_3',B_1486,C_1487)
      | ~ m1_subset_1(C_1487,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_5420])).

tff(c_5432,plain,(
    ! [B_1486] :
      ( ~ l1_orders_2('#skF_3')
      | ~ r2_hidden('#skF_1'('#skF_3',B_1486,'#skF_7'),'#skF_5')
      | r2_lattice3('#skF_3',B_1486,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_5424,c_24])).

tff(c_5442,plain,(
    ! [B_1488] :
      ( ~ r2_hidden('#skF_1'('#skF_3',B_1488,'#skF_7'),'#skF_5')
      | r2_lattice3('#skF_3',B_1488,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_62,c_5432])).

tff(c_5450,plain,
    ( r2_lattice3('#skF_3','#skF_5','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_5442])).

tff(c_5456,plain,(
    r2_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_5450])).

tff(c_5458,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2157,c_5456])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 21:06:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.48/3.03  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.48/3.03  
% 8.48/3.03  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.48/3.04  %$ r3_orders_2 > r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_finset_1 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_6
% 8.48/3.04  
% 8.48/3.04  %Foreground sorts:
% 8.48/3.04  
% 8.48/3.04  
% 8.48/3.04  %Background operators:
% 8.48/3.04  
% 8.48/3.04  
% 8.48/3.04  %Foreground operators:
% 8.48/3.04  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.48/3.04  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 8.48/3.04  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 8.48/3.04  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 8.48/3.04  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 8.48/3.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.48/3.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.48/3.04  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.48/3.04  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 8.48/3.04  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.48/3.04  tff('#skF_7', type, '#skF_7': $i).
% 8.48/3.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.48/3.04  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 8.48/3.04  tff('#skF_5', type, '#skF_5': $i).
% 8.48/3.04  tff('#skF_3', type, '#skF_3': $i).
% 8.48/3.04  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.48/3.04  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 8.48/3.04  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 8.48/3.04  tff(r1_yellow_0, type, r1_yellow_0: ($i * $i) > $o).
% 8.48/3.04  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.48/3.04  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 8.48/3.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.48/3.04  tff('#skF_4', type, '#skF_4': $i).
% 8.48/3.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.48/3.04  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.48/3.04  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.48/3.04  tff(v1_finset_1, type, v1_finset_1: $i > $o).
% 8.48/3.04  tff('#skF_6', type, '#skF_6': $i > $i).
% 8.48/3.04  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.48/3.04  
% 8.75/3.06  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 8.75/3.06  tff(f_198, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((((![D]: ((v1_finset_1(D) & m1_subset_1(D, k1_zfmisc_1(B))) => (~(D = k1_xboole_0) => r1_yellow_0(A, D)))) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => ~(r2_hidden(D, C) & (![E]: ((v1_finset_1(E) & m1_subset_1(E, k1_zfmisc_1(B))) => ~(r1_yellow_0(A, E) & (D = k1_yellow_0(A, E))))))))) & (![D]: ((v1_finset_1(D) & m1_subset_1(D, k1_zfmisc_1(B))) => (~(D = k1_xboole_0) => r2_hidden(k1_yellow_0(A, D), C))))) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, B, D) <=> r2_lattice3(A, C, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_waybel_0)).
% 8.75/3.06  tff(f_81, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, D, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattice3)).
% 8.75/3.06  tff(f_33, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 8.75/3.06  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 8.75/3.06  tff(f_39, axiom, (![A]: v1_finset_1(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_finset_1)).
% 8.75/3.06  tff(f_67, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => r3_orders_2(A, B, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r3_orders_2)).
% 8.75/3.06  tff(f_54, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 8.75/3.06  tff(f_123, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((((r1_lattice3(A, k1_tarski(C), B) => r1_orders_2(A, B, C)) & (r1_orders_2(A, B, C) => r1_lattice3(A, k1_tarski(C), B))) & (r2_lattice3(A, k1_tarski(C), B) => r1_orders_2(A, C, B))) & (r1_orders_2(A, C, B) => r2_lattice3(A, k1_tarski(C), B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_yellow_0)).
% 8.75/3.06  tff(f_99, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_yellow_0(A, B) => ((C = k1_yellow_0(A, B)) <=> (r2_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, B, D) => r1_orders_2(A, C, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_yellow_0)).
% 8.75/3.06  tff(f_139, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (r1_tarski(B, C) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r1_lattice3(A, C, D) => r1_lattice3(A, B, D)) & (r2_lattice3(A, C, D) => r2_lattice3(A, B, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_yellow_0)).
% 8.75/3.06  tff(f_29, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 8.75/3.06  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 8.75/3.06  tff(c_70, plain, (~r2_lattice3('#skF_3', '#skF_5', '#skF_7') | ~r2_lattice3('#skF_3', '#skF_4', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_198])).
% 8.75/3.06  tff(c_107, plain, (~r2_lattice3('#skF_3', '#skF_4', '#skF_7')), inference(splitLeft, [status(thm)], [c_70])).
% 8.75/3.06  tff(c_62, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_198])).
% 8.75/3.06  tff(c_52, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_198])).
% 8.75/3.06  tff(c_26, plain, (![A_13, B_20, C_21]: (r2_hidden('#skF_1'(A_13, B_20, C_21), B_20) | r2_lattice3(A_13, B_20, C_21) | ~m1_subset_1(C_21, u1_struct_0(A_13)) | ~l1_orders_2(A_13))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.75/3.06  tff(c_8, plain, (![A_2, B_3]: (r1_tarski(k1_tarski(A_2), B_3) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.75/3.06  tff(c_12, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.75/3.06  tff(c_14, plain, (![A_6]: (v1_finset_1(k1_tarski(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.75/3.06  tff(c_28, plain, (![A_13, B_20, C_21]: (m1_subset_1('#skF_1'(A_13, B_20, C_21), u1_struct_0(A_13)) | r2_lattice3(A_13, B_20, C_21) | ~m1_subset_1(C_21, u1_struct_0(A_13)) | ~l1_orders_2(A_13))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.75/3.06  tff(c_68, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_198])).
% 8.75/3.06  tff(c_66, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_198])).
% 8.75/3.06  tff(c_198, plain, (![A_145, B_146, C_147]: (r3_orders_2(A_145, B_146, B_146) | ~m1_subset_1(C_147, u1_struct_0(A_145)) | ~m1_subset_1(B_146, u1_struct_0(A_145)) | ~l1_orders_2(A_145) | ~v3_orders_2(A_145) | v2_struct_0(A_145))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.75/3.06  tff(c_202, plain, (![B_146]: (r3_orders_2('#skF_3', B_146, B_146) | ~m1_subset_1(B_146, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_52, c_198])).
% 8.75/3.06  tff(c_206, plain, (![B_146]: (r3_orders_2('#skF_3', B_146, B_146) | ~m1_subset_1(B_146, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_202])).
% 8.75/3.06  tff(c_208, plain, (![B_148]: (r3_orders_2('#skF_3', B_148, B_148) | ~m1_subset_1(B_148, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_68, c_206])).
% 8.75/3.06  tff(c_211, plain, (![B_20, C_21]: (r3_orders_2('#skF_3', '#skF_1'('#skF_3', B_20, C_21), '#skF_1'('#skF_3', B_20, C_21)) | r2_lattice3('#skF_3', B_20, C_21) | ~m1_subset_1(C_21, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_28, c_208])).
% 8.75/3.06  tff(c_216, plain, (![B_20, C_21]: (r3_orders_2('#skF_3', '#skF_1'('#skF_3', B_20, C_21), '#skF_1'('#skF_3', B_20, C_21)) | r2_lattice3('#skF_3', B_20, C_21) | ~m1_subset_1(C_21, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_211])).
% 8.75/3.06  tff(c_322, plain, (![A_184, B_185, C_186]: (r1_orders_2(A_184, B_185, C_186) | ~r3_orders_2(A_184, B_185, C_186) | ~m1_subset_1(C_186, u1_struct_0(A_184)) | ~m1_subset_1(B_185, u1_struct_0(A_184)) | ~l1_orders_2(A_184) | ~v3_orders_2(A_184) | v2_struct_0(A_184))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.75/3.06  tff(c_324, plain, (![B_20, C_21]: (r1_orders_2('#skF_3', '#skF_1'('#skF_3', B_20, C_21), '#skF_1'('#skF_3', B_20, C_21)) | ~m1_subset_1('#skF_1'('#skF_3', B_20, C_21), u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3') | r2_lattice3('#skF_3', B_20, C_21) | ~m1_subset_1(C_21, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_216, c_322])).
% 8.75/3.06  tff(c_329, plain, (![B_20, C_21]: (r1_orders_2('#skF_3', '#skF_1'('#skF_3', B_20, C_21), '#skF_1'('#skF_3', B_20, C_21)) | ~m1_subset_1('#skF_1'('#skF_3', B_20, C_21), u1_struct_0('#skF_3')) | v2_struct_0('#skF_3') | r2_lattice3('#skF_3', B_20, C_21) | ~m1_subset_1(C_21, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_324])).
% 8.75/3.06  tff(c_330, plain, (![B_20, C_21]: (r1_orders_2('#skF_3', '#skF_1'('#skF_3', B_20, C_21), '#skF_1'('#skF_3', B_20, C_21)) | ~m1_subset_1('#skF_1'('#skF_3', B_20, C_21), u1_struct_0('#skF_3')) | r2_lattice3('#skF_3', B_20, C_21) | ~m1_subset_1(C_21, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_68, c_329])).
% 8.75/3.06  tff(c_116, plain, (![D_115]: (r1_yellow_0('#skF_3', D_115) | k1_xboole_0=D_115 | ~m1_subset_1(D_115, k1_zfmisc_1('#skF_4')) | ~v1_finset_1(D_115))), inference(cnfTransformation, [status(thm)], [f_198])).
% 8.75/3.06  tff(c_121, plain, (![A_4]: (r1_yellow_0('#skF_3', A_4) | k1_xboole_0=A_4 | ~v1_finset_1(A_4) | ~r1_tarski(A_4, '#skF_4'))), inference(resolution, [status(thm)], [c_12, c_116])).
% 8.75/3.06  tff(c_40, plain, (![A_37, C_43, B_41]: (r2_lattice3(A_37, k1_tarski(C_43), B_41) | ~r1_orders_2(A_37, C_43, B_41) | ~m1_subset_1(C_43, u1_struct_0(A_37)) | ~m1_subset_1(B_41, u1_struct_0(A_37)) | ~l1_orders_2(A_37))), inference(cnfTransformation, [status(thm)], [f_123])).
% 8.75/3.06  tff(c_34, plain, (![A_25, B_32, C_33]: (m1_subset_1('#skF_2'(A_25, B_32, C_33), u1_struct_0(A_25)) | k1_yellow_0(A_25, B_32)=C_33 | ~r2_lattice3(A_25, B_32, C_33) | ~r1_yellow_0(A_25, B_32) | ~m1_subset_1(C_33, u1_struct_0(A_25)) | ~l1_orders_2(A_25))), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.75/3.06  tff(c_355, plain, (![A_199, B_200, C_201]: (r2_lattice3(A_199, B_200, '#skF_2'(A_199, B_200, C_201)) | k1_yellow_0(A_199, B_200)=C_201 | ~r2_lattice3(A_199, B_200, C_201) | ~r1_yellow_0(A_199, B_200) | ~m1_subset_1(C_201, u1_struct_0(A_199)) | ~l1_orders_2(A_199))), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.75/3.06  tff(c_42, plain, (![A_37, C_43, B_41]: (r1_orders_2(A_37, C_43, B_41) | ~r2_lattice3(A_37, k1_tarski(C_43), B_41) | ~m1_subset_1(C_43, u1_struct_0(A_37)) | ~m1_subset_1(B_41, u1_struct_0(A_37)) | ~l1_orders_2(A_37))), inference(cnfTransformation, [status(thm)], [f_123])).
% 8.75/3.06  tff(c_1114, plain, (![A_412, C_413, C_414]: (r1_orders_2(A_412, C_413, '#skF_2'(A_412, k1_tarski(C_413), C_414)) | ~m1_subset_1(C_413, u1_struct_0(A_412)) | ~m1_subset_1('#skF_2'(A_412, k1_tarski(C_413), C_414), u1_struct_0(A_412)) | k1_yellow_0(A_412, k1_tarski(C_413))=C_414 | ~r2_lattice3(A_412, k1_tarski(C_413), C_414) | ~r1_yellow_0(A_412, k1_tarski(C_413)) | ~m1_subset_1(C_414, u1_struct_0(A_412)) | ~l1_orders_2(A_412))), inference(resolution, [status(thm)], [c_355, c_42])).
% 8.75/3.06  tff(c_1119, plain, (![A_415, C_416, C_417]: (r1_orders_2(A_415, C_416, '#skF_2'(A_415, k1_tarski(C_416), C_417)) | ~m1_subset_1(C_416, u1_struct_0(A_415)) | k1_yellow_0(A_415, k1_tarski(C_416))=C_417 | ~r2_lattice3(A_415, k1_tarski(C_416), C_417) | ~r1_yellow_0(A_415, k1_tarski(C_416)) | ~m1_subset_1(C_417, u1_struct_0(A_415)) | ~l1_orders_2(A_415))), inference(resolution, [status(thm)], [c_34, c_1114])).
% 8.75/3.06  tff(c_30, plain, (![A_25, C_33, B_32]: (~r1_orders_2(A_25, C_33, '#skF_2'(A_25, B_32, C_33)) | k1_yellow_0(A_25, B_32)=C_33 | ~r2_lattice3(A_25, B_32, C_33) | ~r1_yellow_0(A_25, B_32) | ~m1_subset_1(C_33, u1_struct_0(A_25)) | ~l1_orders_2(A_25))), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.75/3.06  tff(c_1131, plain, (![A_418, C_419]: (k1_yellow_0(A_418, k1_tarski(C_419))=C_419 | ~r2_lattice3(A_418, k1_tarski(C_419), C_419) | ~r1_yellow_0(A_418, k1_tarski(C_419)) | ~m1_subset_1(C_419, u1_struct_0(A_418)) | ~l1_orders_2(A_418))), inference(resolution, [status(thm)], [c_1119, c_30])).
% 8.75/3.06  tff(c_1306, plain, (![A_436, B_437]: (k1_yellow_0(A_436, k1_tarski(B_437))=B_437 | ~r1_yellow_0(A_436, k1_tarski(B_437)) | ~r1_orders_2(A_436, B_437, B_437) | ~m1_subset_1(B_437, u1_struct_0(A_436)) | ~l1_orders_2(A_436))), inference(resolution, [status(thm)], [c_40, c_1131])).
% 8.75/3.06  tff(c_1309, plain, (![B_437]: (k1_yellow_0('#skF_3', k1_tarski(B_437))=B_437 | ~r1_orders_2('#skF_3', B_437, B_437) | ~m1_subset_1(B_437, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | k1_tarski(B_437)=k1_xboole_0 | ~v1_finset_1(k1_tarski(B_437)) | ~r1_tarski(k1_tarski(B_437), '#skF_4'))), inference(resolution, [status(thm)], [c_121, c_1306])).
% 8.75/3.06  tff(c_1313, plain, (![B_438]: (k1_yellow_0('#skF_3', k1_tarski(B_438))=B_438 | ~r1_orders_2('#skF_3', B_438, B_438) | ~m1_subset_1(B_438, u1_struct_0('#skF_3')) | k1_tarski(B_438)=k1_xboole_0 | ~r1_tarski(k1_tarski(B_438), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_62, c_1309])).
% 8.75/3.06  tff(c_1432, plain, (![B_460, C_461]: (k1_yellow_0('#skF_3', k1_tarski('#skF_1'('#skF_3', B_460, C_461)))='#skF_1'('#skF_3', B_460, C_461) | k1_tarski('#skF_1'('#skF_3', B_460, C_461))=k1_xboole_0 | ~r1_tarski(k1_tarski('#skF_1'('#skF_3', B_460, C_461)), '#skF_4') | ~m1_subset_1('#skF_1'('#skF_3', B_460, C_461), u1_struct_0('#skF_3')) | r2_lattice3('#skF_3', B_460, C_461) | ~m1_subset_1(C_461, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_330, c_1313])).
% 8.75/3.06  tff(c_1899, plain, (![B_588, C_589]: (k1_yellow_0('#skF_3', k1_tarski('#skF_1'('#skF_3', B_588, C_589)))='#skF_1'('#skF_3', B_588, C_589) | k1_tarski('#skF_1'('#skF_3', B_588, C_589))=k1_xboole_0 | ~m1_subset_1('#skF_1'('#skF_3', B_588, C_589), u1_struct_0('#skF_3')) | r2_lattice3('#skF_3', B_588, C_589) | ~m1_subset_1(C_589, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_1'('#skF_3', B_588, C_589), '#skF_4'))), inference(resolution, [status(thm)], [c_8, c_1432])).
% 8.75/3.06  tff(c_1903, plain, (![B_20, C_21]: (k1_yellow_0('#skF_3', k1_tarski('#skF_1'('#skF_3', B_20, C_21)))='#skF_1'('#skF_3', B_20, C_21) | k1_tarski('#skF_1'('#skF_3', B_20, C_21))=k1_xboole_0 | ~r2_hidden('#skF_1'('#skF_3', B_20, C_21), '#skF_4') | r2_lattice3('#skF_3', B_20, C_21) | ~m1_subset_1(C_21, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_28, c_1899])).
% 8.75/3.06  tff(c_1907, plain, (![B_590, C_591]: (k1_yellow_0('#skF_3', k1_tarski('#skF_1'('#skF_3', B_590, C_591)))='#skF_1'('#skF_3', B_590, C_591) | k1_tarski('#skF_1'('#skF_3', B_590, C_591))=k1_xboole_0 | ~r2_hidden('#skF_1'('#skF_3', B_590, C_591), '#skF_4') | r2_lattice3('#skF_3', B_590, C_591) | ~m1_subset_1(C_591, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1903])).
% 8.75/3.06  tff(c_54, plain, (![D_102]: (r2_hidden(k1_yellow_0('#skF_3', D_102), '#skF_5') | k1_xboole_0=D_102 | ~m1_subset_1(D_102, k1_zfmisc_1('#skF_4')) | ~v1_finset_1(D_102))), inference(cnfTransformation, [status(thm)], [f_198])).
% 8.75/3.06  tff(c_1919, plain, (![B_590, C_591]: (r2_hidden('#skF_1'('#skF_3', B_590, C_591), '#skF_5') | k1_tarski('#skF_1'('#skF_3', B_590, C_591))=k1_xboole_0 | ~m1_subset_1(k1_tarski('#skF_1'('#skF_3', B_590, C_591)), k1_zfmisc_1('#skF_4')) | ~v1_finset_1(k1_tarski('#skF_1'('#skF_3', B_590, C_591))) | k1_tarski('#skF_1'('#skF_3', B_590, C_591))=k1_xboole_0 | ~r2_hidden('#skF_1'('#skF_3', B_590, C_591), '#skF_4') | r2_lattice3('#skF_3', B_590, C_591) | ~m1_subset_1(C_591, u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1907, c_54])).
% 8.75/3.06  tff(c_1933, plain, (![B_592, C_593]: (r2_hidden('#skF_1'('#skF_3', B_592, C_593), '#skF_5') | ~m1_subset_1(k1_tarski('#skF_1'('#skF_3', B_592, C_593)), k1_zfmisc_1('#skF_4')) | k1_tarski('#skF_1'('#skF_3', B_592, C_593))=k1_xboole_0 | ~r2_hidden('#skF_1'('#skF_3', B_592, C_593), '#skF_4') | r2_lattice3('#skF_3', B_592, C_593) | ~m1_subset_1(C_593, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1919])).
% 8.75/3.06  tff(c_1938, plain, (![B_594, C_595]: (r2_hidden('#skF_1'('#skF_3', B_594, C_595), '#skF_5') | k1_tarski('#skF_1'('#skF_3', B_594, C_595))=k1_xboole_0 | ~r2_hidden('#skF_1'('#skF_3', B_594, C_595), '#skF_4') | r2_lattice3('#skF_3', B_594, C_595) | ~m1_subset_1(C_595, u1_struct_0('#skF_3')) | ~r1_tarski(k1_tarski('#skF_1'('#skF_3', B_594, C_595)), '#skF_4'))), inference(resolution, [status(thm)], [c_12, c_1933])).
% 8.75/3.06  tff(c_1943, plain, (![B_596, C_597]: (r2_hidden('#skF_1'('#skF_3', B_596, C_597), '#skF_5') | k1_tarski('#skF_1'('#skF_3', B_596, C_597))=k1_xboole_0 | r2_lattice3('#skF_3', B_596, C_597) | ~m1_subset_1(C_597, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_1'('#skF_3', B_596, C_597), '#skF_4'))), inference(resolution, [status(thm)], [c_8, c_1938])).
% 8.75/3.06  tff(c_76, plain, (r2_lattice3('#skF_3', '#skF_4', '#skF_7') | r2_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_198])).
% 8.75/3.06  tff(c_108, plain, (r2_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_107, c_76])).
% 8.75/3.06  tff(c_140, plain, (![A_124, B_125, D_126, C_127]: (r2_lattice3(A_124, B_125, D_126) | ~r2_lattice3(A_124, C_127, D_126) | ~m1_subset_1(D_126, u1_struct_0(A_124)) | ~r1_tarski(B_125, C_127) | ~l1_orders_2(A_124))), inference(cnfTransformation, [status(thm)], [f_139])).
% 8.75/3.06  tff(c_142, plain, (![B_125]: (r2_lattice3('#skF_3', B_125, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~r1_tarski(B_125, '#skF_5') | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_108, c_140])).
% 8.75/3.06  tff(c_145, plain, (![B_125]: (r2_lattice3('#skF_3', B_125, '#skF_7') | ~r1_tarski(B_125, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_52, c_142])).
% 8.75/3.06  tff(c_228, plain, (![A_157, C_158, B_159]: (r1_orders_2(A_157, C_158, B_159) | ~r2_lattice3(A_157, k1_tarski(C_158), B_159) | ~m1_subset_1(C_158, u1_struct_0(A_157)) | ~m1_subset_1(B_159, u1_struct_0(A_157)) | ~l1_orders_2(A_157))), inference(cnfTransformation, [status(thm)], [f_123])).
% 8.75/3.06  tff(c_232, plain, (![C_158]: (r1_orders_2('#skF_3', C_158, '#skF_7') | ~m1_subset_1(C_158, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~r1_tarski(k1_tarski(C_158), '#skF_5'))), inference(resolution, [status(thm)], [c_145, c_228])).
% 8.75/3.06  tff(c_237, plain, (![C_162]: (r1_orders_2('#skF_3', C_162, '#skF_7') | ~m1_subset_1(C_162, u1_struct_0('#skF_3')) | ~r1_tarski(k1_tarski(C_162), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_52, c_232])).
% 8.75/3.06  tff(c_243, plain, (![A_163]: (r1_orders_2('#skF_3', A_163, '#skF_7') | ~m1_subset_1(A_163, u1_struct_0('#skF_3')) | ~r2_hidden(A_163, '#skF_5'))), inference(resolution, [status(thm)], [c_8, c_237])).
% 8.75/3.06  tff(c_247, plain, (![B_20, C_21]: (r1_orders_2('#skF_3', '#skF_1'('#skF_3', B_20, C_21), '#skF_7') | ~r2_hidden('#skF_1'('#skF_3', B_20, C_21), '#skF_5') | r2_lattice3('#skF_3', B_20, C_21) | ~m1_subset_1(C_21, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_28, c_243])).
% 8.75/3.06  tff(c_305, plain, (![B_178, C_179]: (r1_orders_2('#skF_3', '#skF_1'('#skF_3', B_178, C_179), '#skF_7') | ~r2_hidden('#skF_1'('#skF_3', B_178, C_179), '#skF_5') | r2_lattice3('#skF_3', B_178, C_179) | ~m1_subset_1(C_179, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_247])).
% 8.75/3.06  tff(c_24, plain, (![A_13, B_20, C_21]: (~r1_orders_2(A_13, '#skF_1'(A_13, B_20, C_21), C_21) | r2_lattice3(A_13, B_20, C_21) | ~m1_subset_1(C_21, u1_struct_0(A_13)) | ~l1_orders_2(A_13))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.75/3.06  tff(c_309, plain, (![B_178]: (~l1_orders_2('#skF_3') | ~r2_hidden('#skF_1'('#skF_3', B_178, '#skF_7'), '#skF_5') | r2_lattice3('#skF_3', B_178, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_305, c_24])).
% 8.75/3.06  tff(c_312, plain, (![B_178]: (~r2_hidden('#skF_1'('#skF_3', B_178, '#skF_7'), '#skF_5') | r2_lattice3('#skF_3', B_178, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_62, c_309])).
% 8.75/3.06  tff(c_1952, plain, (![B_596]: (k1_tarski('#skF_1'('#skF_3', B_596, '#skF_7'))=k1_xboole_0 | r2_lattice3('#skF_3', B_596, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~r2_hidden('#skF_1'('#skF_3', B_596, '#skF_7'), '#skF_4'))), inference(resolution, [status(thm)], [c_1943, c_312])).
% 8.75/3.06  tff(c_1964, plain, (![B_598]: (k1_tarski('#skF_1'('#skF_3', B_598, '#skF_7'))=k1_xboole_0 | r2_lattice3('#skF_3', B_598, '#skF_7') | ~r2_hidden('#skF_1'('#skF_3', B_598, '#skF_7'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1952])).
% 8.75/3.06  tff(c_1968, plain, (k1_tarski('#skF_1'('#skF_3', '#skF_4', '#skF_7'))=k1_xboole_0 | r2_lattice3('#skF_3', '#skF_4', '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_26, c_1964])).
% 8.75/3.06  tff(c_1971, plain, (k1_tarski('#skF_1'('#skF_3', '#skF_4', '#skF_7'))=k1_xboole_0 | r2_lattice3('#skF_3', '#skF_4', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_52, c_1968])).
% 8.75/3.06  tff(c_1972, plain, (k1_tarski('#skF_1'('#skF_3', '#skF_4', '#skF_7'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_107, c_1971])).
% 8.75/3.06  tff(c_4, plain, (![A_1]: (~v1_xboole_0(k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.75/3.06  tff(c_2107, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1972, c_4])).
% 8.75/3.06  tff(c_2156, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_2107])).
% 8.75/3.06  tff(c_2157, plain, (~r2_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_70])).
% 8.75/3.06  tff(c_2175, plain, (![D_603]: (m1_subset_1('#skF_6'(D_603), k1_zfmisc_1('#skF_4')) | ~r2_hidden(D_603, '#skF_5') | ~m1_subset_1(D_603, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_198])).
% 8.75/3.06  tff(c_10, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.75/3.06  tff(c_2183, plain, (![D_603]: (r1_tarski('#skF_6'(D_603), '#skF_4') | ~r2_hidden(D_603, '#skF_5') | ~m1_subset_1(D_603, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_2175, c_10])).
% 8.75/3.06  tff(c_80, plain, (![D_100]: (r1_yellow_0('#skF_3', '#skF_6'(D_100)) | ~r2_hidden(D_100, '#skF_5') | ~m1_subset_1(D_100, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_198])).
% 8.75/3.06  tff(c_2158, plain, (r2_lattice3('#skF_3', '#skF_4', '#skF_7')), inference(splitRight, [status(thm)], [c_70])).
% 8.75/3.06  tff(c_2192, plain, (![A_610, B_611, D_612, C_613]: (r2_lattice3(A_610, B_611, D_612) | ~r2_lattice3(A_610, C_613, D_612) | ~m1_subset_1(D_612, u1_struct_0(A_610)) | ~r1_tarski(B_611, C_613) | ~l1_orders_2(A_610))), inference(cnfTransformation, [status(thm)], [f_139])).
% 8.75/3.06  tff(c_2194, plain, (![B_611]: (r2_lattice3('#skF_3', B_611, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~r1_tarski(B_611, '#skF_4') | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_2158, c_2192])).
% 8.75/3.06  tff(c_2197, plain, (![B_611]: (r2_lattice3('#skF_3', B_611, '#skF_7') | ~r1_tarski(B_611, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_52, c_2194])).
% 8.75/3.06  tff(c_2234, plain, (![A_626, B_627, C_628]: (m1_subset_1('#skF_1'(A_626, B_627, C_628), u1_struct_0(A_626)) | r2_lattice3(A_626, B_627, C_628) | ~m1_subset_1(C_628, u1_struct_0(A_626)) | ~l1_orders_2(A_626))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.75/3.06  tff(c_78, plain, (![D_100]: (k1_yellow_0('#skF_3', '#skF_6'(D_100))=D_100 | ~r2_hidden(D_100, '#skF_5') | ~m1_subset_1(D_100, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_198])).
% 8.75/3.06  tff(c_2238, plain, (![B_627, C_628]: (k1_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_627, C_628)))='#skF_1'('#skF_3', B_627, C_628) | ~r2_hidden('#skF_1'('#skF_3', B_627, C_628), '#skF_5') | r2_lattice3('#skF_3', B_627, C_628) | ~m1_subset_1(C_628, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_2234, c_78])).
% 8.75/3.06  tff(c_2245, plain, (![B_627, C_628]: (k1_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_627, C_628)))='#skF_1'('#skF_3', B_627, C_628) | ~r2_hidden('#skF_1'('#skF_3', B_627, C_628), '#skF_5') | r2_lattice3('#skF_3', B_627, C_628) | ~m1_subset_1(C_628, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_2238])).
% 8.75/3.06  tff(c_2578, plain, (![B_731, C_732]: (k1_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_731, C_732)))='#skF_1'('#skF_3', B_731, C_732) | ~r2_hidden('#skF_1'('#skF_3', B_731, C_732), '#skF_5') | r2_lattice3('#skF_3', B_731, C_732) | ~m1_subset_1(C_732, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_2238])).
% 8.75/3.06  tff(c_36, plain, (![A_25, B_32, D_36]: (r1_orders_2(A_25, k1_yellow_0(A_25, B_32), D_36) | ~r2_lattice3(A_25, B_32, D_36) | ~m1_subset_1(D_36, u1_struct_0(A_25)) | ~r1_yellow_0(A_25, B_32) | ~m1_subset_1(k1_yellow_0(A_25, B_32), u1_struct_0(A_25)) | ~l1_orders_2(A_25))), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.75/3.06  tff(c_2583, plain, (![B_731, C_732, D_36]: (r1_orders_2('#skF_3', k1_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_731, C_732))), D_36) | ~r2_lattice3('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_731, C_732)), D_36) | ~m1_subset_1(D_36, u1_struct_0('#skF_3')) | ~r1_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_731, C_732))) | ~m1_subset_1('#skF_1'('#skF_3', B_731, C_732), u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~r2_hidden('#skF_1'('#skF_3', B_731, C_732), '#skF_5') | r2_lattice3('#skF_3', B_731, C_732) | ~m1_subset_1(C_732, u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2578, c_36])).
% 8.75/3.06  tff(c_3964, plain, (![B_1072, C_1073, D_1074]: (r1_orders_2('#skF_3', k1_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_1072, C_1073))), D_1074) | ~r2_lattice3('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_1072, C_1073)), D_1074) | ~m1_subset_1(D_1074, u1_struct_0('#skF_3')) | ~r1_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_1072, C_1073))) | ~m1_subset_1('#skF_1'('#skF_3', B_1072, C_1073), u1_struct_0('#skF_3')) | ~r2_hidden('#skF_1'('#skF_3', B_1072, C_1073), '#skF_5') | r2_lattice3('#skF_3', B_1072, C_1073) | ~m1_subset_1(C_1073, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_2583])).
% 8.75/3.06  tff(c_5325, plain, (![B_1472, C_1473, D_1474]: (r1_orders_2('#skF_3', '#skF_1'('#skF_3', B_1472, C_1473), D_1474) | ~r2_lattice3('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_1472, C_1473)), D_1474) | ~m1_subset_1(D_1474, u1_struct_0('#skF_3')) | ~r1_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_1472, C_1473))) | ~m1_subset_1('#skF_1'('#skF_3', B_1472, C_1473), u1_struct_0('#skF_3')) | ~r2_hidden('#skF_1'('#skF_3', B_1472, C_1473), '#skF_5') | r2_lattice3('#skF_3', B_1472, C_1473) | ~m1_subset_1(C_1473, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_1'('#skF_3', B_1472, C_1473), '#skF_5') | r2_lattice3('#skF_3', B_1472, C_1473) | ~m1_subset_1(C_1473, u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2245, c_3964])).
% 8.75/3.06  tff(c_5367, plain, (![B_1472, C_1473]: (r1_orders_2('#skF_3', '#skF_1'('#skF_3', B_1472, C_1473), '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~r1_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_1472, C_1473))) | ~m1_subset_1('#skF_1'('#skF_3', B_1472, C_1473), u1_struct_0('#skF_3')) | ~r2_hidden('#skF_1'('#skF_3', B_1472, C_1473), '#skF_5') | r2_lattice3('#skF_3', B_1472, C_1473) | ~m1_subset_1(C_1473, u1_struct_0('#skF_3')) | ~r1_tarski('#skF_6'('#skF_1'('#skF_3', B_1472, C_1473)), '#skF_4'))), inference(resolution, [status(thm)], [c_2197, c_5325])).
% 8.75/3.06  tff(c_5402, plain, (![B_1480, C_1481]: (r1_orders_2('#skF_3', '#skF_1'('#skF_3', B_1480, C_1481), '#skF_7') | ~r1_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_1480, C_1481))) | ~m1_subset_1('#skF_1'('#skF_3', B_1480, C_1481), u1_struct_0('#skF_3')) | ~r2_hidden('#skF_1'('#skF_3', B_1480, C_1481), '#skF_5') | r2_lattice3('#skF_3', B_1480, C_1481) | ~m1_subset_1(C_1481, u1_struct_0('#skF_3')) | ~r1_tarski('#skF_6'('#skF_1'('#skF_3', B_1480, C_1481)), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_5367])).
% 8.75/3.06  tff(c_5411, plain, (![B_1482, C_1483]: (r1_orders_2('#skF_3', '#skF_1'('#skF_3', B_1482, C_1483), '#skF_7') | r2_lattice3('#skF_3', B_1482, C_1483) | ~m1_subset_1(C_1483, u1_struct_0('#skF_3')) | ~r1_tarski('#skF_6'('#skF_1'('#skF_3', B_1482, C_1483)), '#skF_4') | ~r2_hidden('#skF_1'('#skF_3', B_1482, C_1483), '#skF_5') | ~m1_subset_1('#skF_1'('#skF_3', B_1482, C_1483), u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_80, c_5402])).
% 8.75/3.06  tff(c_5416, plain, (![B_1484, C_1485]: (r1_orders_2('#skF_3', '#skF_1'('#skF_3', B_1484, C_1485), '#skF_7') | r2_lattice3('#skF_3', B_1484, C_1485) | ~m1_subset_1(C_1485, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_1'('#skF_3', B_1484, C_1485), '#skF_5') | ~m1_subset_1('#skF_1'('#skF_3', B_1484, C_1485), u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_2183, c_5411])).
% 8.75/3.06  tff(c_5420, plain, (![B_20, C_21]: (r1_orders_2('#skF_3', '#skF_1'('#skF_3', B_20, C_21), '#skF_7') | ~r2_hidden('#skF_1'('#skF_3', B_20, C_21), '#skF_5') | r2_lattice3('#skF_3', B_20, C_21) | ~m1_subset_1(C_21, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_28, c_5416])).
% 8.75/3.06  tff(c_5424, plain, (![B_1486, C_1487]: (r1_orders_2('#skF_3', '#skF_1'('#skF_3', B_1486, C_1487), '#skF_7') | ~r2_hidden('#skF_1'('#skF_3', B_1486, C_1487), '#skF_5') | r2_lattice3('#skF_3', B_1486, C_1487) | ~m1_subset_1(C_1487, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_5420])).
% 8.75/3.06  tff(c_5432, plain, (![B_1486]: (~l1_orders_2('#skF_3') | ~r2_hidden('#skF_1'('#skF_3', B_1486, '#skF_7'), '#skF_5') | r2_lattice3('#skF_3', B_1486, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_5424, c_24])).
% 8.75/3.06  tff(c_5442, plain, (![B_1488]: (~r2_hidden('#skF_1'('#skF_3', B_1488, '#skF_7'), '#skF_5') | r2_lattice3('#skF_3', B_1488, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_62, c_5432])).
% 8.75/3.06  tff(c_5450, plain, (r2_lattice3('#skF_3', '#skF_5', '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_26, c_5442])).
% 8.75/3.06  tff(c_5456, plain, (r2_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_52, c_5450])).
% 8.75/3.06  tff(c_5458, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2157, c_5456])).
% 8.75/3.06  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.75/3.06  
% 8.75/3.06  Inference rules
% 8.75/3.06  ----------------------
% 8.75/3.06  #Ref     : 0
% 8.75/3.06  #Sup     : 1059
% 8.75/3.06  #Fact    : 0
% 8.75/3.06  #Define  : 0
% 8.75/3.06  #Split   : 14
% 8.75/3.06  #Chain   : 0
% 8.75/3.06  #Close   : 0
% 8.75/3.06  
% 8.75/3.06  Ordering : KBO
% 8.75/3.06  
% 8.75/3.06  Simplification rules
% 8.75/3.06  ----------------------
% 8.75/3.06  #Subsume      : 272
% 8.75/3.06  #Demod        : 698
% 8.75/3.06  #Tautology    : 54
% 8.75/3.06  #SimpNegUnit  : 113
% 8.75/3.06  #BackRed      : 0
% 8.75/3.06  
% 8.75/3.06  #Partial instantiations: 0
% 8.75/3.06  #Strategies tried      : 1
% 8.75/3.06  
% 8.75/3.06  Timing (in seconds)
% 8.75/3.06  ----------------------
% 8.75/3.07  Preprocessing        : 0.37
% 8.75/3.07  Parsing              : 0.18
% 8.75/3.07  CNF conversion       : 0.03
% 8.75/3.07  Main loop            : 1.90
% 8.75/3.07  Inferencing          : 0.72
% 8.75/3.07  Reduction            : 0.49
% 8.75/3.07  Demodulation         : 0.30
% 8.75/3.07  BG Simplification    : 0.06
% 8.75/3.07  Subsumption          : 0.49
% 8.75/3.07  Abstraction          : 0.08
% 8.75/3.07  MUC search           : 0.00
% 8.75/3.07  Cooper               : 0.00
% 8.75/3.07  Total                : 2.31
% 8.75/3.07  Index Insertion      : 0.00
% 8.75/3.07  Index Deletion       : 0.00
% 8.75/3.07  Index Matching       : 0.00
% 8.75/3.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
