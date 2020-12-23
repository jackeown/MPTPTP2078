%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:03 EST 2020

% Result     : Theorem 8.97s
% Output     : CNFRefutation 9.04s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 238 expanded)
%              Number of leaves         :   41 ( 101 expanded)
%              Depth                    :   22
%              Number of atoms          :  445 (1577 expanded)
%              Number of equality atoms :   37 ( 166 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_yellow_0 > r2_hidden > r1_tarski > m1_subset_1 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_finset_1 > l1_orders_2 > k2_yellow_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

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

tff(r2_yellow_0,type,(
    r2_yellow_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k2_yellow_0,type,(
    k2_yellow_0: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

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
                         => r2_yellow_0(A,D) ) )
                    & ! [D] :
                        ( m1_subset_1(D,u1_struct_0(A))
                       => ~ ( r2_hidden(D,C)
                            & ! [E] :
                                ( ( v1_finset_1(E)
                                  & m1_subset_1(E,k1_zfmisc_1(B)) )
                               => ~ ( r2_yellow_0(A,E)
                                    & D = k2_yellow_0(A,E) ) ) ) )
                    & ! [D] :
                        ( ( v1_finset_1(D)
                          & m1_subset_1(D,k1_zfmisc_1(B)) )
                       => ( D != k1_xboole_0
                         => r2_hidden(k2_yellow_0(A,D),C) ) ) )
                 => ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r1_lattice3(A,B,D)
                      <=> r1_lattice3(A,C,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_waybel_0)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r1_lattice3(A,B,C)
          <=> ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_hidden(D,B)
                 => r1_orders_2(A,C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattice3)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

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
         => ( r2_yellow_0(A,B)
           => ( C = k2_yellow_0(A,B)
            <=> ( r1_lattice3(A,B,C)
                & ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r1_lattice3(A,B,D)
                     => r1_orders_2(A,D,C) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_yellow_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

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

tff(c_74,plain,
    ( r1_lattice3('#skF_3','#skF_4','#skF_7')
    | r1_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_99,plain,(
    r1_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_68,plain,
    ( ~ r1_lattice3('#skF_3','#skF_5','#skF_7')
    | ~ r1_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_101,plain,(
    ~ r1_lattice3('#skF_3','#skF_4','#skF_7') ),
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
      | r1_lattice3(A_13,B_20,C_21)
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
      | r1_lattice3(A_13,B_20,C_21)
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
      | r1_lattice3('#skF_3',B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26,c_215])).

tff(c_223,plain,(
    ! [B_20,C_21] :
      ( r3_orders_2('#skF_3','#skF_1'('#skF_3',B_20,C_21),'#skF_1'('#skF_3',B_20,C_21))
      | r1_lattice3('#skF_3',B_20,C_21)
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
      | r1_lattice3('#skF_3',B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_223,c_329])).

tff(c_336,plain,(
    ! [B_20,C_21] :
      ( r1_orders_2('#skF_3','#skF_1'('#skF_3',B_20,C_21),'#skF_1'('#skF_3',B_20,C_21))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_20,C_21),u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3')
      | r1_lattice3('#skF_3',B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_331])).

tff(c_337,plain,(
    ! [B_20,C_21] :
      ( r1_orders_2('#skF_3','#skF_1'('#skF_3',B_20,C_21),'#skF_1'('#skF_3',B_20,C_21))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_20,C_21),u1_struct_0('#skF_3'))
      | r1_lattice3('#skF_3',B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_336])).

tff(c_115,plain,(
    ! [D_115] :
      ( r2_yellow_0('#skF_3',D_115)
      | k1_xboole_0 = D_115
      | ~ m1_subset_1(D_115,k1_zfmisc_1('#skF_4'))
      | ~ v1_finset_1(D_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_119,plain,(
    ! [A_2] :
      ( r2_yellow_0('#skF_3',k1_tarski(A_2))
      | k1_tarski(A_2) = k1_xboole_0
      | ~ v1_finset_1(k1_tarski(A_2))
      | ~ r2_hidden(A_2,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_6,c_115])).

tff(c_126,plain,(
    ! [A_2] :
      ( r2_yellow_0('#skF_3',k1_tarski(A_2))
      | k1_tarski(A_2) = k1_xboole_0
      | ~ r2_hidden(A_2,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_119])).

tff(c_42,plain,(
    ! [A_37,C_43,B_41] :
      ( r1_lattice3(A_37,k1_tarski(C_43),B_41)
      | ~ r1_orders_2(A_37,B_41,C_43)
      | ~ m1_subset_1(C_43,u1_struct_0(A_37))
      | ~ m1_subset_1(B_41,u1_struct_0(A_37))
      | ~ l1_orders_2(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_32,plain,(
    ! [A_25,B_32,C_33] :
      ( m1_subset_1('#skF_2'(A_25,B_32,C_33),u1_struct_0(A_25))
      | k2_yellow_0(A_25,B_32) = C_33
      | ~ r1_lattice3(A_25,B_32,C_33)
      | ~ r2_yellow_0(A_25,B_32)
      | ~ m1_subset_1(C_33,u1_struct_0(A_25))
      | ~ l1_orders_2(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_521,plain,(
    ! [A_232,B_233,C_234] :
      ( r1_lattice3(A_232,B_233,'#skF_2'(A_232,B_233,C_234))
      | k2_yellow_0(A_232,B_233) = C_234
      | ~ r1_lattice3(A_232,B_233,C_234)
      | ~ r2_yellow_0(A_232,B_233)
      | ~ m1_subset_1(C_234,u1_struct_0(A_232))
      | ~ l1_orders_2(A_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_44,plain,(
    ! [A_37,B_41,C_43] :
      ( r1_orders_2(A_37,B_41,C_43)
      | ~ r1_lattice3(A_37,k1_tarski(C_43),B_41)
      | ~ m1_subset_1(C_43,u1_struct_0(A_37))
      | ~ m1_subset_1(B_41,u1_struct_0(A_37))
      | ~ l1_orders_2(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1131,plain,(
    ! [A_409,C_410,C_411] :
      ( r1_orders_2(A_409,'#skF_2'(A_409,k1_tarski(C_410),C_411),C_410)
      | ~ m1_subset_1(C_410,u1_struct_0(A_409))
      | ~ m1_subset_1('#skF_2'(A_409,k1_tarski(C_410),C_411),u1_struct_0(A_409))
      | k2_yellow_0(A_409,k1_tarski(C_410)) = C_411
      | ~ r1_lattice3(A_409,k1_tarski(C_410),C_411)
      | ~ r2_yellow_0(A_409,k1_tarski(C_410))
      | ~ m1_subset_1(C_411,u1_struct_0(A_409))
      | ~ l1_orders_2(A_409) ) ),
    inference(resolution,[status(thm)],[c_521,c_44])).

tff(c_1154,plain,(
    ! [A_425,C_426,C_427] :
      ( r1_orders_2(A_425,'#skF_2'(A_425,k1_tarski(C_426),C_427),C_426)
      | ~ m1_subset_1(C_426,u1_struct_0(A_425))
      | k2_yellow_0(A_425,k1_tarski(C_426)) = C_427
      | ~ r1_lattice3(A_425,k1_tarski(C_426),C_427)
      | ~ r2_yellow_0(A_425,k1_tarski(C_426))
      | ~ m1_subset_1(C_427,u1_struct_0(A_425))
      | ~ l1_orders_2(A_425) ) ),
    inference(resolution,[status(thm)],[c_32,c_1131])).

tff(c_28,plain,(
    ! [A_25,B_32,C_33] :
      ( ~ r1_orders_2(A_25,'#skF_2'(A_25,B_32,C_33),C_33)
      | k2_yellow_0(A_25,B_32) = C_33
      | ~ r1_lattice3(A_25,B_32,C_33)
      | ~ r2_yellow_0(A_25,B_32)
      | ~ m1_subset_1(C_33,u1_struct_0(A_25))
      | ~ l1_orders_2(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1166,plain,(
    ! [A_428,C_429] :
      ( k2_yellow_0(A_428,k1_tarski(C_429)) = C_429
      | ~ r1_lattice3(A_428,k1_tarski(C_429),C_429)
      | ~ r2_yellow_0(A_428,k1_tarski(C_429))
      | ~ m1_subset_1(C_429,u1_struct_0(A_428))
      | ~ l1_orders_2(A_428) ) ),
    inference(resolution,[status(thm)],[c_1154,c_28])).

tff(c_1348,plain,(
    ! [A_441,B_442] :
      ( k2_yellow_0(A_441,k1_tarski(B_442)) = B_442
      | ~ r2_yellow_0(A_441,k1_tarski(B_442))
      | ~ r1_orders_2(A_441,B_442,B_442)
      | ~ m1_subset_1(B_442,u1_struct_0(A_441))
      | ~ l1_orders_2(A_441) ) ),
    inference(resolution,[status(thm)],[c_42,c_1166])).

tff(c_1353,plain,(
    ! [A_2] :
      ( k2_yellow_0('#skF_3',k1_tarski(A_2)) = A_2
      | ~ r1_orders_2('#skF_3',A_2,A_2)
      | ~ m1_subset_1(A_2,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | k1_tarski(A_2) = k1_xboole_0
      | ~ r2_hidden(A_2,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_126,c_1348])).

tff(c_1373,plain,(
    ! [A_448] :
      ( k2_yellow_0('#skF_3',k1_tarski(A_448)) = A_448
      | ~ r1_orders_2('#skF_3',A_448,A_448)
      | ~ m1_subset_1(A_448,u1_struct_0('#skF_3'))
      | k1_tarski(A_448) = k1_xboole_0
      | ~ r2_hidden(A_448,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1353])).

tff(c_1463,plain,(
    ! [B_451,C_452] :
      ( k2_yellow_0('#skF_3',k1_tarski('#skF_1'('#skF_3',B_451,C_452))) = '#skF_1'('#skF_3',B_451,C_452)
      | k1_tarski('#skF_1'('#skF_3',B_451,C_452)) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_451,C_452),'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_3',B_451,C_452),u1_struct_0('#skF_3'))
      | r1_lattice3('#skF_3',B_451,C_452)
      | ~ m1_subset_1(C_452,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_337,c_1373])).

tff(c_1467,plain,(
    ! [B_20,C_21] :
      ( k2_yellow_0('#skF_3',k1_tarski('#skF_1'('#skF_3',B_20,C_21))) = '#skF_1'('#skF_3',B_20,C_21)
      | k1_tarski('#skF_1'('#skF_3',B_20,C_21)) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_20,C_21),'#skF_4')
      | r1_lattice3('#skF_3',B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26,c_1463])).

tff(c_1477,plain,(
    ! [B_454,C_455] :
      ( k2_yellow_0('#skF_3',k1_tarski('#skF_1'('#skF_3',B_454,C_455))) = '#skF_1'('#skF_3',B_454,C_455)
      | k1_tarski('#skF_1'('#skF_3',B_454,C_455)) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_454,C_455),'#skF_4')
      | r1_lattice3('#skF_3',B_454,C_455)
      | ~ m1_subset_1(C_455,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1467])).

tff(c_52,plain,(
    ! [D_102] :
      ( r2_hidden(k2_yellow_0('#skF_3',D_102),'#skF_5')
      | k1_xboole_0 = D_102
      | ~ m1_subset_1(D_102,k1_zfmisc_1('#skF_4'))
      | ~ v1_finset_1(D_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_1489,plain,(
    ! [B_454,C_455] :
      ( r2_hidden('#skF_1'('#skF_3',B_454,C_455),'#skF_5')
      | k1_tarski('#skF_1'('#skF_3',B_454,C_455)) = k1_xboole_0
      | ~ m1_subset_1(k1_tarski('#skF_1'('#skF_3',B_454,C_455)),k1_zfmisc_1('#skF_4'))
      | ~ v1_finset_1(k1_tarski('#skF_1'('#skF_3',B_454,C_455)))
      | k1_tarski('#skF_1'('#skF_3',B_454,C_455)) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_454,C_455),'#skF_4')
      | r1_lattice3('#skF_3',B_454,C_455)
      | ~ m1_subset_1(C_455,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1477,c_52])).

tff(c_1566,plain,(
    ! [B_474,C_475] :
      ( r2_hidden('#skF_1'('#skF_3',B_474,C_475),'#skF_5')
      | ~ m1_subset_1(k1_tarski('#skF_1'('#skF_3',B_474,C_475)),k1_zfmisc_1('#skF_4'))
      | k1_tarski('#skF_1'('#skF_3',B_474,C_475)) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_474,C_475),'#skF_4')
      | r1_lattice3('#skF_3',B_474,C_475)
      | ~ m1_subset_1(C_475,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1489])).

tff(c_1580,plain,(
    ! [B_478,C_479] :
      ( r2_hidden('#skF_1'('#skF_3',B_478,C_479),'#skF_5')
      | k1_tarski('#skF_1'('#skF_3',B_478,C_479)) = k1_xboole_0
      | r1_lattice3('#skF_3',B_478,C_479)
      | ~ m1_subset_1(C_479,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'('#skF_3',B_478,C_479),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_6,c_1566])).

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

tff(c_147,plain,(
    ! [A_125,B_126,D_127,C_128] :
      ( r1_lattice3(A_125,B_126,D_127)
      | ~ r1_lattice3(A_125,C_128,D_127)
      | ~ m1_subset_1(D_127,u1_struct_0(A_125))
      | ~ r1_tarski(B_126,C_128)
      | ~ l1_orders_2(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_149,plain,(
    ! [B_126] :
      ( r1_lattice3('#skF_3',B_126,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ r1_tarski(B_126,'#skF_5')
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_99,c_147])).

tff(c_152,plain,(
    ! [B_126] :
      ( r1_lattice3('#skF_3',B_126,'#skF_7')
      | ~ r1_tarski(B_126,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_149])).

tff(c_225,plain,(
    ! [A_150,B_151,C_152] :
      ( r1_orders_2(A_150,B_151,C_152)
      | ~ r1_lattice3(A_150,k1_tarski(C_152),B_151)
      | ~ m1_subset_1(C_152,u1_struct_0(A_150))
      | ~ m1_subset_1(B_151,u1_struct_0(A_150))
      | ~ l1_orders_2(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_229,plain,(
    ! [C_152] :
      ( r1_orders_2('#skF_3','#skF_7',C_152)
      | ~ m1_subset_1(C_152,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ r1_tarski(k1_tarski(C_152),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_152,c_225])).

tff(c_233,plain,(
    ! [C_153] :
      ( r1_orders_2('#skF_3','#skF_7',C_153)
      | ~ m1_subset_1(C_153,u1_struct_0('#skF_3'))
      | ~ r1_tarski(k1_tarski(C_153),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_229])).

tff(c_239,plain,(
    ! [A_154] :
      ( r1_orders_2('#skF_3','#skF_7',A_154)
      | ~ m1_subset_1(A_154,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_154,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_106,c_233])).

tff(c_243,plain,(
    ! [B_20,C_21] :
      ( r1_orders_2('#skF_3','#skF_7','#skF_1'('#skF_3',B_20,C_21))
      | ~ r2_hidden('#skF_1'('#skF_3',B_20,C_21),'#skF_5')
      | r1_lattice3('#skF_3',B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26,c_239])).

tff(c_312,plain,(
    ! [B_179,C_180] :
      ( r1_orders_2('#skF_3','#skF_7','#skF_1'('#skF_3',B_179,C_180))
      | ~ r2_hidden('#skF_1'('#skF_3',B_179,C_180),'#skF_5')
      | r1_lattice3('#skF_3',B_179,C_180)
      | ~ m1_subset_1(C_180,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_243])).

tff(c_22,plain,(
    ! [A_13,C_21,B_20] :
      ( ~ r1_orders_2(A_13,C_21,'#skF_1'(A_13,B_20,C_21))
      | r1_lattice3(A_13,B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0(A_13))
      | ~ l1_orders_2(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_316,plain,(
    ! [B_179] :
      ( ~ l1_orders_2('#skF_3')
      | ~ r2_hidden('#skF_1'('#skF_3',B_179,'#skF_7'),'#skF_5')
      | r1_lattice3('#skF_3',B_179,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_312,c_22])).

tff(c_319,plain,(
    ! [B_179] :
      ( ~ r2_hidden('#skF_1'('#skF_3',B_179,'#skF_7'),'#skF_5')
      | r1_lattice3('#skF_3',B_179,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_60,c_316])).

tff(c_1586,plain,(
    ! [B_478] :
      ( k1_tarski('#skF_1'('#skF_3',B_478,'#skF_7')) = k1_xboole_0
      | r1_lattice3('#skF_3',B_478,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'('#skF_3',B_478,'#skF_7'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1580,c_319])).

tff(c_1597,plain,(
    ! [B_480] :
      ( k1_tarski('#skF_1'('#skF_3',B_480,'#skF_7')) = k1_xboole_0
      | r1_lattice3('#skF_3',B_480,'#skF_7')
      | ~ r2_hidden('#skF_1'('#skF_3',B_480,'#skF_7'),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1586])).

tff(c_1601,plain,
    ( k1_tarski('#skF_1'('#skF_3','#skF_4','#skF_7')) = k1_xboole_0
    | r1_lattice3('#skF_3','#skF_4','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_1597])).

tff(c_1604,plain,
    ( k1_tarski('#skF_1'('#skF_3','#skF_4','#skF_7')) = k1_xboole_0
    | r1_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_1601])).

tff(c_1605,plain,(
    k1_tarski('#skF_1'('#skF_3','#skF_4','#skF_7')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_1604])).

tff(c_4,plain,(
    ! [A_1] : ~ v1_xboole_0(k1_tarski(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1729,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1605,c_4])).

tff(c_1774,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1729])).

tff(c_1776,plain,(
    ~ r1_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_1812,plain,(
    ! [D_491] :
      ( m1_subset_1('#skF_6'(D_491),k1_zfmisc_1('#skF_4'))
      | ~ r2_hidden(D_491,'#skF_5')
      | ~ m1_subset_1(D_491,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_1820,plain,(
    ! [D_491] :
      ( r1_tarski('#skF_6'(D_491),'#skF_4')
      | ~ r2_hidden(D_491,'#skF_5')
      | ~ m1_subset_1(D_491,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1812,c_8])).

tff(c_78,plain,(
    ! [D_100] :
      ( r2_yellow_0('#skF_3','#skF_6'(D_100))
      | ~ r2_hidden(D_100,'#skF_5')
      | ~ m1_subset_1(D_100,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_1775,plain,(
    r1_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_1824,plain,(
    ! [A_497,B_498,D_499,C_500] :
      ( r1_lattice3(A_497,B_498,D_499)
      | ~ r1_lattice3(A_497,C_500,D_499)
      | ~ m1_subset_1(D_499,u1_struct_0(A_497))
      | ~ r1_tarski(B_498,C_500)
      | ~ l1_orders_2(A_497) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1826,plain,(
    ! [B_498] :
      ( r1_lattice3('#skF_3',B_498,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ r1_tarski(B_498,'#skF_4')
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1775,c_1824])).

tff(c_1829,plain,(
    ! [B_498] :
      ( r1_lattice3('#skF_3',B_498,'#skF_7')
      | ~ r1_tarski(B_498,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_1826])).

tff(c_1871,plain,(
    ! [A_512,B_513,C_514] :
      ( m1_subset_1('#skF_1'(A_512,B_513,C_514),u1_struct_0(A_512))
      | r1_lattice3(A_512,B_513,C_514)
      | ~ m1_subset_1(C_514,u1_struct_0(A_512))
      | ~ l1_orders_2(A_512) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_76,plain,(
    ! [D_100] :
      ( k2_yellow_0('#skF_3','#skF_6'(D_100)) = D_100
      | ~ r2_hidden(D_100,'#skF_5')
      | ~ m1_subset_1(D_100,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_1875,plain,(
    ! [B_513,C_514] :
      ( k2_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_513,C_514))) = '#skF_1'('#skF_3',B_513,C_514)
      | ~ r2_hidden('#skF_1'('#skF_3',B_513,C_514),'#skF_5')
      | r1_lattice3('#skF_3',B_513,C_514)
      | ~ m1_subset_1(C_514,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1871,c_76])).

tff(c_1882,plain,(
    ! [B_513,C_514] :
      ( k2_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_513,C_514))) = '#skF_1'('#skF_3',B_513,C_514)
      | ~ r2_hidden('#skF_1'('#skF_3',B_513,C_514),'#skF_5')
      | r1_lattice3('#skF_3',B_513,C_514)
      | ~ m1_subset_1(C_514,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1875])).

tff(c_2221,plain,(
    ! [A_614,D_615,B_616] :
      ( r1_orders_2(A_614,D_615,k2_yellow_0(A_614,B_616))
      | ~ r1_lattice3(A_614,B_616,D_615)
      | ~ m1_subset_1(D_615,u1_struct_0(A_614))
      | ~ r2_yellow_0(A_614,B_616)
      | ~ m1_subset_1(k2_yellow_0(A_614,B_616),u1_struct_0(A_614))
      | ~ l1_orders_2(A_614) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2223,plain,(
    ! [D_615,B_513,C_514] :
      ( r1_orders_2('#skF_3',D_615,k2_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_513,C_514))))
      | ~ r1_lattice3('#skF_3','#skF_6'('#skF_1'('#skF_3',B_513,C_514)),D_615)
      | ~ m1_subset_1(D_615,u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_513,C_514)))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_513,C_514),u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ r2_hidden('#skF_1'('#skF_3',B_513,C_514),'#skF_5')
      | r1_lattice3('#skF_3',B_513,C_514)
      | ~ m1_subset_1(C_514,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1882,c_2221])).

tff(c_3586,plain,(
    ! [D_932,B_933,C_934] :
      ( r1_orders_2('#skF_3',D_932,k2_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_933,C_934))))
      | ~ r1_lattice3('#skF_3','#skF_6'('#skF_1'('#skF_3',B_933,C_934)),D_932)
      | ~ m1_subset_1(D_932,u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_933,C_934)))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_933,C_934),u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'('#skF_3',B_933,C_934),'#skF_5')
      | r1_lattice3('#skF_3',B_933,C_934)
      | ~ m1_subset_1(C_934,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2223])).

tff(c_4993,plain,(
    ! [D_1326,B_1327,C_1328] :
      ( r1_orders_2('#skF_3',D_1326,'#skF_1'('#skF_3',B_1327,C_1328))
      | ~ r1_lattice3('#skF_3','#skF_6'('#skF_1'('#skF_3',B_1327,C_1328)),D_1326)
      | ~ m1_subset_1(D_1326,u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_1327,C_1328)))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_1327,C_1328),u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'('#skF_3',B_1327,C_1328),'#skF_5')
      | r1_lattice3('#skF_3',B_1327,C_1328)
      | ~ m1_subset_1(C_1328,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'('#skF_3',B_1327,C_1328),'#skF_5')
      | r1_lattice3('#skF_3',B_1327,C_1328)
      | ~ m1_subset_1(C_1328,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1882,c_3586])).

tff(c_5035,plain,(
    ! [B_1327,C_1328] :
      ( r1_orders_2('#skF_3','#skF_7','#skF_1'('#skF_3',B_1327,C_1328))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_1327,C_1328)))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_1327,C_1328),u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'('#skF_3',B_1327,C_1328),'#skF_5')
      | r1_lattice3('#skF_3',B_1327,C_1328)
      | ~ m1_subset_1(C_1328,u1_struct_0('#skF_3'))
      | ~ r1_tarski('#skF_6'('#skF_1'('#skF_3',B_1327,C_1328)),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1829,c_4993])).

tff(c_5065,plain,(
    ! [B_1329,C_1330] :
      ( r1_orders_2('#skF_3','#skF_7','#skF_1'('#skF_3',B_1329,C_1330))
      | ~ r2_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_1329,C_1330)))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_1329,C_1330),u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'('#skF_3',B_1329,C_1330),'#skF_5')
      | r1_lattice3('#skF_3',B_1329,C_1330)
      | ~ m1_subset_1(C_1330,u1_struct_0('#skF_3'))
      | ~ r1_tarski('#skF_6'('#skF_1'('#skF_3',B_1329,C_1330)),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_5035])).

tff(c_5074,plain,(
    ! [B_1331,C_1332] :
      ( r1_orders_2('#skF_3','#skF_7','#skF_1'('#skF_3',B_1331,C_1332))
      | r1_lattice3('#skF_3',B_1331,C_1332)
      | ~ m1_subset_1(C_1332,u1_struct_0('#skF_3'))
      | ~ r1_tarski('#skF_6'('#skF_1'('#skF_3',B_1331,C_1332)),'#skF_4')
      | ~ r2_hidden('#skF_1'('#skF_3',B_1331,C_1332),'#skF_5')
      | ~ m1_subset_1('#skF_1'('#skF_3',B_1331,C_1332),u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_78,c_5065])).

tff(c_5079,plain,(
    ! [B_1333,C_1334] :
      ( r1_orders_2('#skF_3','#skF_7','#skF_1'('#skF_3',B_1333,C_1334))
      | r1_lattice3('#skF_3',B_1333,C_1334)
      | ~ m1_subset_1(C_1334,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'('#skF_3',B_1333,C_1334),'#skF_5')
      | ~ m1_subset_1('#skF_1'('#skF_3',B_1333,C_1334),u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1820,c_5074])).

tff(c_5083,plain,(
    ! [B_20,C_21] :
      ( r1_orders_2('#skF_3','#skF_7','#skF_1'('#skF_3',B_20,C_21))
      | ~ r2_hidden('#skF_1'('#skF_3',B_20,C_21),'#skF_5')
      | r1_lattice3('#skF_3',B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26,c_5079])).

tff(c_5087,plain,(
    ! [B_1335,C_1336] :
      ( r1_orders_2('#skF_3','#skF_7','#skF_1'('#skF_3',B_1335,C_1336))
      | ~ r2_hidden('#skF_1'('#skF_3',B_1335,C_1336),'#skF_5')
      | r1_lattice3('#skF_3',B_1335,C_1336)
      | ~ m1_subset_1(C_1336,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_5083])).

tff(c_5095,plain,(
    ! [B_1335] :
      ( ~ l1_orders_2('#skF_3')
      | ~ r2_hidden('#skF_1'('#skF_3',B_1335,'#skF_7'),'#skF_5')
      | r1_lattice3('#skF_3',B_1335,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_5087,c_22])).

tff(c_5105,plain,(
    ! [B_1337] :
      ( ~ r2_hidden('#skF_1'('#skF_3',B_1337,'#skF_7'),'#skF_5')
      | r1_lattice3('#skF_3',B_1337,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_60,c_5095])).

tff(c_5113,plain,
    ( r1_lattice3('#skF_3','#skF_5','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_5105])).

tff(c_5119,plain,(
    r1_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_5113])).

tff(c_5121,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1776,c_5119])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:31:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.97/3.02  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.97/3.03  
% 8.97/3.03  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.04/3.03  %$ r3_orders_2 > r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_yellow_0 > r2_hidden > r1_tarski > m1_subset_1 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_finset_1 > l1_orders_2 > k2_yellow_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_6
% 9.04/3.03  
% 9.04/3.03  %Foreground sorts:
% 9.04/3.03  
% 9.04/3.03  
% 9.04/3.03  %Background operators:
% 9.04/3.03  
% 9.04/3.03  
% 9.04/3.03  %Foreground operators:
% 9.04/3.03  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 9.04/3.03  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 9.04/3.03  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 9.04/3.03  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 9.04/3.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.04/3.03  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.04/3.03  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.04/3.03  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 9.04/3.03  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.04/3.03  tff('#skF_7', type, '#skF_7': $i).
% 9.04/3.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.04/3.03  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 9.04/3.03  tff('#skF_5', type, '#skF_5': $i).
% 9.04/3.03  tff(r2_yellow_0, type, r2_yellow_0: ($i * $i) > $o).
% 9.04/3.03  tff('#skF_3', type, '#skF_3': $i).
% 9.04/3.03  tff(k2_yellow_0, type, k2_yellow_0: ($i * $i) > $i).
% 9.04/3.03  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 9.04/3.03  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 9.04/3.03  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 9.04/3.03  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.04/3.03  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 9.04/3.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.04/3.03  tff('#skF_4', type, '#skF_4': $i).
% 9.04/3.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.04/3.03  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.04/3.03  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.04/3.03  tff(v1_finset_1, type, v1_finset_1: $i > $o).
% 9.04/3.03  tff('#skF_6', type, '#skF_6': $i > $i).
% 9.04/3.03  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.04/3.03  
% 9.04/3.06  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 9.04/3.06  tff(f_198, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((((![D]: ((v1_finset_1(D) & m1_subset_1(D, k1_zfmisc_1(B))) => (~(D = k1_xboole_0) => r2_yellow_0(A, D)))) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => ~(r2_hidden(D, C) & (![E]: ((v1_finset_1(E) & m1_subset_1(E, k1_zfmisc_1(B))) => ~(r2_yellow_0(A, E) & (D = k2_yellow_0(A, E))))))))) & (![D]: ((v1_finset_1(D) & m1_subset_1(D, k1_zfmisc_1(B))) => (~(D = k1_xboole_0) => r2_hidden(k2_yellow_0(A, D), C))))) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r1_lattice3(A, B, D) <=> r1_lattice3(A, C, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_waybel_0)).
% 9.04/3.06  tff(f_81, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, C, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_lattice3)).
% 9.04/3.06  tff(f_33, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 9.04/3.06  tff(f_39, axiom, (![A]: v1_finset_1(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_finset_1)).
% 9.04/3.06  tff(f_67, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => r3_orders_2(A, B, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r3_orders_2)).
% 9.04/3.06  tff(f_54, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 9.04/3.06  tff(f_123, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((((r1_lattice3(A, k1_tarski(C), B) => r1_orders_2(A, B, C)) & (r1_orders_2(A, B, C) => r1_lattice3(A, k1_tarski(C), B))) & (r2_lattice3(A, k1_tarski(C), B) => r1_orders_2(A, C, B))) & (r1_orders_2(A, C, B) => r2_lattice3(A, k1_tarski(C), B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_yellow_0)).
% 9.04/3.06  tff(f_99, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_yellow_0(A, B) => ((C = k2_yellow_0(A, B)) <=> (r1_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r1_lattice3(A, B, D) => r1_orders_2(A, D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_yellow_0)).
% 9.04/3.06  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 9.04/3.06  tff(f_139, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (r1_tarski(B, C) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r1_lattice3(A, C, D) => r1_lattice3(A, B, D)) & (r2_lattice3(A, C, D) => r2_lattice3(A, B, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_yellow_0)).
% 9.04/3.06  tff(f_29, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 9.04/3.06  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 9.04/3.06  tff(c_74, plain, (r1_lattice3('#skF_3', '#skF_4', '#skF_7') | r1_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_198])).
% 9.04/3.06  tff(c_99, plain, (r1_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(splitLeft, [status(thm)], [c_74])).
% 9.04/3.06  tff(c_68, plain, (~r1_lattice3('#skF_3', '#skF_5', '#skF_7') | ~r1_lattice3('#skF_3', '#skF_4', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_198])).
% 9.04/3.06  tff(c_101, plain, (~r1_lattice3('#skF_3', '#skF_4', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_99, c_68])).
% 9.04/3.06  tff(c_60, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_198])).
% 9.04/3.06  tff(c_50, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_198])).
% 9.04/3.06  tff(c_24, plain, (![A_13, B_20, C_21]: (r2_hidden('#skF_1'(A_13, B_20, C_21), B_20) | r1_lattice3(A_13, B_20, C_21) | ~m1_subset_1(C_21, u1_struct_0(A_13)) | ~l1_orders_2(A_13))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.04/3.06  tff(c_6, plain, (![A_2, B_3]: (m1_subset_1(k1_tarski(A_2), k1_zfmisc_1(B_3)) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.04/3.06  tff(c_12, plain, (![A_6]: (v1_finset_1(k1_tarski(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.04/3.06  tff(c_26, plain, (![A_13, B_20, C_21]: (m1_subset_1('#skF_1'(A_13, B_20, C_21), u1_struct_0(A_13)) | r1_lattice3(A_13, B_20, C_21) | ~m1_subset_1(C_21, u1_struct_0(A_13)) | ~l1_orders_2(A_13))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.04/3.06  tff(c_66, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_198])).
% 9.04/3.06  tff(c_64, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_198])).
% 9.04/3.06  tff(c_205, plain, (![A_146, B_147, C_148]: (r3_orders_2(A_146, B_147, B_147) | ~m1_subset_1(C_148, u1_struct_0(A_146)) | ~m1_subset_1(B_147, u1_struct_0(A_146)) | ~l1_orders_2(A_146) | ~v3_orders_2(A_146) | v2_struct_0(A_146))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.04/3.06  tff(c_209, plain, (![B_147]: (r3_orders_2('#skF_3', B_147, B_147) | ~m1_subset_1(B_147, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_205])).
% 9.04/3.06  tff(c_213, plain, (![B_147]: (r3_orders_2('#skF_3', B_147, B_147) | ~m1_subset_1(B_147, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_209])).
% 9.04/3.06  tff(c_215, plain, (![B_149]: (r3_orders_2('#skF_3', B_149, B_149) | ~m1_subset_1(B_149, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_66, c_213])).
% 9.04/3.06  tff(c_218, plain, (![B_20, C_21]: (r3_orders_2('#skF_3', '#skF_1'('#skF_3', B_20, C_21), '#skF_1'('#skF_3', B_20, C_21)) | r1_lattice3('#skF_3', B_20, C_21) | ~m1_subset_1(C_21, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_26, c_215])).
% 9.04/3.06  tff(c_223, plain, (![B_20, C_21]: (r3_orders_2('#skF_3', '#skF_1'('#skF_3', B_20, C_21), '#skF_1'('#skF_3', B_20, C_21)) | r1_lattice3('#skF_3', B_20, C_21) | ~m1_subset_1(C_21, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_218])).
% 9.04/3.06  tff(c_329, plain, (![A_185, B_186, C_187]: (r1_orders_2(A_185, B_186, C_187) | ~r3_orders_2(A_185, B_186, C_187) | ~m1_subset_1(C_187, u1_struct_0(A_185)) | ~m1_subset_1(B_186, u1_struct_0(A_185)) | ~l1_orders_2(A_185) | ~v3_orders_2(A_185) | v2_struct_0(A_185))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.04/3.06  tff(c_331, plain, (![B_20, C_21]: (r1_orders_2('#skF_3', '#skF_1'('#skF_3', B_20, C_21), '#skF_1'('#skF_3', B_20, C_21)) | ~m1_subset_1('#skF_1'('#skF_3', B_20, C_21), u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3') | r1_lattice3('#skF_3', B_20, C_21) | ~m1_subset_1(C_21, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_223, c_329])).
% 9.04/3.06  tff(c_336, plain, (![B_20, C_21]: (r1_orders_2('#skF_3', '#skF_1'('#skF_3', B_20, C_21), '#skF_1'('#skF_3', B_20, C_21)) | ~m1_subset_1('#skF_1'('#skF_3', B_20, C_21), u1_struct_0('#skF_3')) | v2_struct_0('#skF_3') | r1_lattice3('#skF_3', B_20, C_21) | ~m1_subset_1(C_21, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_331])).
% 9.04/3.06  tff(c_337, plain, (![B_20, C_21]: (r1_orders_2('#skF_3', '#skF_1'('#skF_3', B_20, C_21), '#skF_1'('#skF_3', B_20, C_21)) | ~m1_subset_1('#skF_1'('#skF_3', B_20, C_21), u1_struct_0('#skF_3')) | r1_lattice3('#skF_3', B_20, C_21) | ~m1_subset_1(C_21, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_66, c_336])).
% 9.04/3.06  tff(c_115, plain, (![D_115]: (r2_yellow_0('#skF_3', D_115) | k1_xboole_0=D_115 | ~m1_subset_1(D_115, k1_zfmisc_1('#skF_4')) | ~v1_finset_1(D_115))), inference(cnfTransformation, [status(thm)], [f_198])).
% 9.04/3.06  tff(c_119, plain, (![A_2]: (r2_yellow_0('#skF_3', k1_tarski(A_2)) | k1_tarski(A_2)=k1_xboole_0 | ~v1_finset_1(k1_tarski(A_2)) | ~r2_hidden(A_2, '#skF_4'))), inference(resolution, [status(thm)], [c_6, c_115])).
% 9.04/3.06  tff(c_126, plain, (![A_2]: (r2_yellow_0('#skF_3', k1_tarski(A_2)) | k1_tarski(A_2)=k1_xboole_0 | ~r2_hidden(A_2, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_119])).
% 9.04/3.06  tff(c_42, plain, (![A_37, C_43, B_41]: (r1_lattice3(A_37, k1_tarski(C_43), B_41) | ~r1_orders_2(A_37, B_41, C_43) | ~m1_subset_1(C_43, u1_struct_0(A_37)) | ~m1_subset_1(B_41, u1_struct_0(A_37)) | ~l1_orders_2(A_37))), inference(cnfTransformation, [status(thm)], [f_123])).
% 9.04/3.06  tff(c_32, plain, (![A_25, B_32, C_33]: (m1_subset_1('#skF_2'(A_25, B_32, C_33), u1_struct_0(A_25)) | k2_yellow_0(A_25, B_32)=C_33 | ~r1_lattice3(A_25, B_32, C_33) | ~r2_yellow_0(A_25, B_32) | ~m1_subset_1(C_33, u1_struct_0(A_25)) | ~l1_orders_2(A_25))), inference(cnfTransformation, [status(thm)], [f_99])).
% 9.04/3.06  tff(c_521, plain, (![A_232, B_233, C_234]: (r1_lattice3(A_232, B_233, '#skF_2'(A_232, B_233, C_234)) | k2_yellow_0(A_232, B_233)=C_234 | ~r1_lattice3(A_232, B_233, C_234) | ~r2_yellow_0(A_232, B_233) | ~m1_subset_1(C_234, u1_struct_0(A_232)) | ~l1_orders_2(A_232))), inference(cnfTransformation, [status(thm)], [f_99])).
% 9.04/3.06  tff(c_44, plain, (![A_37, B_41, C_43]: (r1_orders_2(A_37, B_41, C_43) | ~r1_lattice3(A_37, k1_tarski(C_43), B_41) | ~m1_subset_1(C_43, u1_struct_0(A_37)) | ~m1_subset_1(B_41, u1_struct_0(A_37)) | ~l1_orders_2(A_37))), inference(cnfTransformation, [status(thm)], [f_123])).
% 9.04/3.06  tff(c_1131, plain, (![A_409, C_410, C_411]: (r1_orders_2(A_409, '#skF_2'(A_409, k1_tarski(C_410), C_411), C_410) | ~m1_subset_1(C_410, u1_struct_0(A_409)) | ~m1_subset_1('#skF_2'(A_409, k1_tarski(C_410), C_411), u1_struct_0(A_409)) | k2_yellow_0(A_409, k1_tarski(C_410))=C_411 | ~r1_lattice3(A_409, k1_tarski(C_410), C_411) | ~r2_yellow_0(A_409, k1_tarski(C_410)) | ~m1_subset_1(C_411, u1_struct_0(A_409)) | ~l1_orders_2(A_409))), inference(resolution, [status(thm)], [c_521, c_44])).
% 9.04/3.06  tff(c_1154, plain, (![A_425, C_426, C_427]: (r1_orders_2(A_425, '#skF_2'(A_425, k1_tarski(C_426), C_427), C_426) | ~m1_subset_1(C_426, u1_struct_0(A_425)) | k2_yellow_0(A_425, k1_tarski(C_426))=C_427 | ~r1_lattice3(A_425, k1_tarski(C_426), C_427) | ~r2_yellow_0(A_425, k1_tarski(C_426)) | ~m1_subset_1(C_427, u1_struct_0(A_425)) | ~l1_orders_2(A_425))), inference(resolution, [status(thm)], [c_32, c_1131])).
% 9.04/3.06  tff(c_28, plain, (![A_25, B_32, C_33]: (~r1_orders_2(A_25, '#skF_2'(A_25, B_32, C_33), C_33) | k2_yellow_0(A_25, B_32)=C_33 | ~r1_lattice3(A_25, B_32, C_33) | ~r2_yellow_0(A_25, B_32) | ~m1_subset_1(C_33, u1_struct_0(A_25)) | ~l1_orders_2(A_25))), inference(cnfTransformation, [status(thm)], [f_99])).
% 9.04/3.06  tff(c_1166, plain, (![A_428, C_429]: (k2_yellow_0(A_428, k1_tarski(C_429))=C_429 | ~r1_lattice3(A_428, k1_tarski(C_429), C_429) | ~r2_yellow_0(A_428, k1_tarski(C_429)) | ~m1_subset_1(C_429, u1_struct_0(A_428)) | ~l1_orders_2(A_428))), inference(resolution, [status(thm)], [c_1154, c_28])).
% 9.04/3.06  tff(c_1348, plain, (![A_441, B_442]: (k2_yellow_0(A_441, k1_tarski(B_442))=B_442 | ~r2_yellow_0(A_441, k1_tarski(B_442)) | ~r1_orders_2(A_441, B_442, B_442) | ~m1_subset_1(B_442, u1_struct_0(A_441)) | ~l1_orders_2(A_441))), inference(resolution, [status(thm)], [c_42, c_1166])).
% 9.04/3.06  tff(c_1353, plain, (![A_2]: (k2_yellow_0('#skF_3', k1_tarski(A_2))=A_2 | ~r1_orders_2('#skF_3', A_2, A_2) | ~m1_subset_1(A_2, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | k1_tarski(A_2)=k1_xboole_0 | ~r2_hidden(A_2, '#skF_4'))), inference(resolution, [status(thm)], [c_126, c_1348])).
% 9.04/3.06  tff(c_1373, plain, (![A_448]: (k2_yellow_0('#skF_3', k1_tarski(A_448))=A_448 | ~r1_orders_2('#skF_3', A_448, A_448) | ~m1_subset_1(A_448, u1_struct_0('#skF_3')) | k1_tarski(A_448)=k1_xboole_0 | ~r2_hidden(A_448, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1353])).
% 9.04/3.06  tff(c_1463, plain, (![B_451, C_452]: (k2_yellow_0('#skF_3', k1_tarski('#skF_1'('#skF_3', B_451, C_452)))='#skF_1'('#skF_3', B_451, C_452) | k1_tarski('#skF_1'('#skF_3', B_451, C_452))=k1_xboole_0 | ~r2_hidden('#skF_1'('#skF_3', B_451, C_452), '#skF_4') | ~m1_subset_1('#skF_1'('#skF_3', B_451, C_452), u1_struct_0('#skF_3')) | r1_lattice3('#skF_3', B_451, C_452) | ~m1_subset_1(C_452, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_337, c_1373])).
% 9.04/3.06  tff(c_1467, plain, (![B_20, C_21]: (k2_yellow_0('#skF_3', k1_tarski('#skF_1'('#skF_3', B_20, C_21)))='#skF_1'('#skF_3', B_20, C_21) | k1_tarski('#skF_1'('#skF_3', B_20, C_21))=k1_xboole_0 | ~r2_hidden('#skF_1'('#skF_3', B_20, C_21), '#skF_4') | r1_lattice3('#skF_3', B_20, C_21) | ~m1_subset_1(C_21, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_26, c_1463])).
% 9.04/3.06  tff(c_1477, plain, (![B_454, C_455]: (k2_yellow_0('#skF_3', k1_tarski('#skF_1'('#skF_3', B_454, C_455)))='#skF_1'('#skF_3', B_454, C_455) | k1_tarski('#skF_1'('#skF_3', B_454, C_455))=k1_xboole_0 | ~r2_hidden('#skF_1'('#skF_3', B_454, C_455), '#skF_4') | r1_lattice3('#skF_3', B_454, C_455) | ~m1_subset_1(C_455, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1467])).
% 9.04/3.06  tff(c_52, plain, (![D_102]: (r2_hidden(k2_yellow_0('#skF_3', D_102), '#skF_5') | k1_xboole_0=D_102 | ~m1_subset_1(D_102, k1_zfmisc_1('#skF_4')) | ~v1_finset_1(D_102))), inference(cnfTransformation, [status(thm)], [f_198])).
% 9.04/3.06  tff(c_1489, plain, (![B_454, C_455]: (r2_hidden('#skF_1'('#skF_3', B_454, C_455), '#skF_5') | k1_tarski('#skF_1'('#skF_3', B_454, C_455))=k1_xboole_0 | ~m1_subset_1(k1_tarski('#skF_1'('#skF_3', B_454, C_455)), k1_zfmisc_1('#skF_4')) | ~v1_finset_1(k1_tarski('#skF_1'('#skF_3', B_454, C_455))) | k1_tarski('#skF_1'('#skF_3', B_454, C_455))=k1_xboole_0 | ~r2_hidden('#skF_1'('#skF_3', B_454, C_455), '#skF_4') | r1_lattice3('#skF_3', B_454, C_455) | ~m1_subset_1(C_455, u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1477, c_52])).
% 9.04/3.06  tff(c_1566, plain, (![B_474, C_475]: (r2_hidden('#skF_1'('#skF_3', B_474, C_475), '#skF_5') | ~m1_subset_1(k1_tarski('#skF_1'('#skF_3', B_474, C_475)), k1_zfmisc_1('#skF_4')) | k1_tarski('#skF_1'('#skF_3', B_474, C_475))=k1_xboole_0 | ~r2_hidden('#skF_1'('#skF_3', B_474, C_475), '#skF_4') | r1_lattice3('#skF_3', B_474, C_475) | ~m1_subset_1(C_475, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1489])).
% 9.04/3.06  tff(c_1580, plain, (![B_478, C_479]: (r2_hidden('#skF_1'('#skF_3', B_478, C_479), '#skF_5') | k1_tarski('#skF_1'('#skF_3', B_478, C_479))=k1_xboole_0 | r1_lattice3('#skF_3', B_478, C_479) | ~m1_subset_1(C_479, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_1'('#skF_3', B_478, C_479), '#skF_4'))), inference(resolution, [status(thm)], [c_6, c_1566])).
% 9.04/3.06  tff(c_102, plain, (![A_109, B_110]: (m1_subset_1(k1_tarski(A_109), k1_zfmisc_1(B_110)) | ~r2_hidden(A_109, B_110))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.04/3.06  tff(c_8, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.04/3.06  tff(c_106, plain, (![A_109, B_110]: (r1_tarski(k1_tarski(A_109), B_110) | ~r2_hidden(A_109, B_110))), inference(resolution, [status(thm)], [c_102, c_8])).
% 9.04/3.06  tff(c_147, plain, (![A_125, B_126, D_127, C_128]: (r1_lattice3(A_125, B_126, D_127) | ~r1_lattice3(A_125, C_128, D_127) | ~m1_subset_1(D_127, u1_struct_0(A_125)) | ~r1_tarski(B_126, C_128) | ~l1_orders_2(A_125))), inference(cnfTransformation, [status(thm)], [f_139])).
% 9.04/3.06  tff(c_149, plain, (![B_126]: (r1_lattice3('#skF_3', B_126, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~r1_tarski(B_126, '#skF_5') | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_99, c_147])).
% 9.04/3.06  tff(c_152, plain, (![B_126]: (r1_lattice3('#skF_3', B_126, '#skF_7') | ~r1_tarski(B_126, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_149])).
% 9.04/3.06  tff(c_225, plain, (![A_150, B_151, C_152]: (r1_orders_2(A_150, B_151, C_152) | ~r1_lattice3(A_150, k1_tarski(C_152), B_151) | ~m1_subset_1(C_152, u1_struct_0(A_150)) | ~m1_subset_1(B_151, u1_struct_0(A_150)) | ~l1_orders_2(A_150))), inference(cnfTransformation, [status(thm)], [f_123])).
% 9.04/3.06  tff(c_229, plain, (![C_152]: (r1_orders_2('#skF_3', '#skF_7', C_152) | ~m1_subset_1(C_152, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~r1_tarski(k1_tarski(C_152), '#skF_5'))), inference(resolution, [status(thm)], [c_152, c_225])).
% 9.04/3.06  tff(c_233, plain, (![C_153]: (r1_orders_2('#skF_3', '#skF_7', C_153) | ~m1_subset_1(C_153, u1_struct_0('#skF_3')) | ~r1_tarski(k1_tarski(C_153), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_229])).
% 9.04/3.06  tff(c_239, plain, (![A_154]: (r1_orders_2('#skF_3', '#skF_7', A_154) | ~m1_subset_1(A_154, u1_struct_0('#skF_3')) | ~r2_hidden(A_154, '#skF_5'))), inference(resolution, [status(thm)], [c_106, c_233])).
% 9.04/3.06  tff(c_243, plain, (![B_20, C_21]: (r1_orders_2('#skF_3', '#skF_7', '#skF_1'('#skF_3', B_20, C_21)) | ~r2_hidden('#skF_1'('#skF_3', B_20, C_21), '#skF_5') | r1_lattice3('#skF_3', B_20, C_21) | ~m1_subset_1(C_21, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_26, c_239])).
% 9.04/3.06  tff(c_312, plain, (![B_179, C_180]: (r1_orders_2('#skF_3', '#skF_7', '#skF_1'('#skF_3', B_179, C_180)) | ~r2_hidden('#skF_1'('#skF_3', B_179, C_180), '#skF_5') | r1_lattice3('#skF_3', B_179, C_180) | ~m1_subset_1(C_180, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_243])).
% 9.04/3.06  tff(c_22, plain, (![A_13, C_21, B_20]: (~r1_orders_2(A_13, C_21, '#skF_1'(A_13, B_20, C_21)) | r1_lattice3(A_13, B_20, C_21) | ~m1_subset_1(C_21, u1_struct_0(A_13)) | ~l1_orders_2(A_13))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.04/3.06  tff(c_316, plain, (![B_179]: (~l1_orders_2('#skF_3') | ~r2_hidden('#skF_1'('#skF_3', B_179, '#skF_7'), '#skF_5') | r1_lattice3('#skF_3', B_179, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_312, c_22])).
% 9.04/3.06  tff(c_319, plain, (![B_179]: (~r2_hidden('#skF_1'('#skF_3', B_179, '#skF_7'), '#skF_5') | r1_lattice3('#skF_3', B_179, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_60, c_316])).
% 9.04/3.06  tff(c_1586, plain, (![B_478]: (k1_tarski('#skF_1'('#skF_3', B_478, '#skF_7'))=k1_xboole_0 | r1_lattice3('#skF_3', B_478, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~r2_hidden('#skF_1'('#skF_3', B_478, '#skF_7'), '#skF_4'))), inference(resolution, [status(thm)], [c_1580, c_319])).
% 9.04/3.06  tff(c_1597, plain, (![B_480]: (k1_tarski('#skF_1'('#skF_3', B_480, '#skF_7'))=k1_xboole_0 | r1_lattice3('#skF_3', B_480, '#skF_7') | ~r2_hidden('#skF_1'('#skF_3', B_480, '#skF_7'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1586])).
% 9.04/3.06  tff(c_1601, plain, (k1_tarski('#skF_1'('#skF_3', '#skF_4', '#skF_7'))=k1_xboole_0 | r1_lattice3('#skF_3', '#skF_4', '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_24, c_1597])).
% 9.04/3.06  tff(c_1604, plain, (k1_tarski('#skF_1'('#skF_3', '#skF_4', '#skF_7'))=k1_xboole_0 | r1_lattice3('#skF_3', '#skF_4', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_1601])).
% 9.04/3.06  tff(c_1605, plain, (k1_tarski('#skF_1'('#skF_3', '#skF_4', '#skF_7'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_101, c_1604])).
% 9.04/3.06  tff(c_4, plain, (![A_1]: (~v1_xboole_0(k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.04/3.06  tff(c_1729, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1605, c_4])).
% 9.04/3.06  tff(c_1774, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_1729])).
% 9.04/3.06  tff(c_1776, plain, (~r1_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_74])).
% 9.04/3.06  tff(c_1812, plain, (![D_491]: (m1_subset_1('#skF_6'(D_491), k1_zfmisc_1('#skF_4')) | ~r2_hidden(D_491, '#skF_5') | ~m1_subset_1(D_491, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_198])).
% 9.04/3.06  tff(c_1820, plain, (![D_491]: (r1_tarski('#skF_6'(D_491), '#skF_4') | ~r2_hidden(D_491, '#skF_5') | ~m1_subset_1(D_491, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_1812, c_8])).
% 9.04/3.06  tff(c_78, plain, (![D_100]: (r2_yellow_0('#skF_3', '#skF_6'(D_100)) | ~r2_hidden(D_100, '#skF_5') | ~m1_subset_1(D_100, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_198])).
% 9.04/3.06  tff(c_1775, plain, (r1_lattice3('#skF_3', '#skF_4', '#skF_7')), inference(splitRight, [status(thm)], [c_74])).
% 9.04/3.06  tff(c_1824, plain, (![A_497, B_498, D_499, C_500]: (r1_lattice3(A_497, B_498, D_499) | ~r1_lattice3(A_497, C_500, D_499) | ~m1_subset_1(D_499, u1_struct_0(A_497)) | ~r1_tarski(B_498, C_500) | ~l1_orders_2(A_497))), inference(cnfTransformation, [status(thm)], [f_139])).
% 9.04/3.06  tff(c_1826, plain, (![B_498]: (r1_lattice3('#skF_3', B_498, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~r1_tarski(B_498, '#skF_4') | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_1775, c_1824])).
% 9.04/3.06  tff(c_1829, plain, (![B_498]: (r1_lattice3('#skF_3', B_498, '#skF_7') | ~r1_tarski(B_498, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_1826])).
% 9.04/3.06  tff(c_1871, plain, (![A_512, B_513, C_514]: (m1_subset_1('#skF_1'(A_512, B_513, C_514), u1_struct_0(A_512)) | r1_lattice3(A_512, B_513, C_514) | ~m1_subset_1(C_514, u1_struct_0(A_512)) | ~l1_orders_2(A_512))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.04/3.06  tff(c_76, plain, (![D_100]: (k2_yellow_0('#skF_3', '#skF_6'(D_100))=D_100 | ~r2_hidden(D_100, '#skF_5') | ~m1_subset_1(D_100, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_198])).
% 9.04/3.06  tff(c_1875, plain, (![B_513, C_514]: (k2_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_513, C_514)))='#skF_1'('#skF_3', B_513, C_514) | ~r2_hidden('#skF_1'('#skF_3', B_513, C_514), '#skF_5') | r1_lattice3('#skF_3', B_513, C_514) | ~m1_subset_1(C_514, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_1871, c_76])).
% 9.04/3.06  tff(c_1882, plain, (![B_513, C_514]: (k2_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_513, C_514)))='#skF_1'('#skF_3', B_513, C_514) | ~r2_hidden('#skF_1'('#skF_3', B_513, C_514), '#skF_5') | r1_lattice3('#skF_3', B_513, C_514) | ~m1_subset_1(C_514, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1875])).
% 9.04/3.06  tff(c_2221, plain, (![A_614, D_615, B_616]: (r1_orders_2(A_614, D_615, k2_yellow_0(A_614, B_616)) | ~r1_lattice3(A_614, B_616, D_615) | ~m1_subset_1(D_615, u1_struct_0(A_614)) | ~r2_yellow_0(A_614, B_616) | ~m1_subset_1(k2_yellow_0(A_614, B_616), u1_struct_0(A_614)) | ~l1_orders_2(A_614))), inference(cnfTransformation, [status(thm)], [f_99])).
% 9.04/3.06  tff(c_2223, plain, (![D_615, B_513, C_514]: (r1_orders_2('#skF_3', D_615, k2_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_513, C_514)))) | ~r1_lattice3('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_513, C_514)), D_615) | ~m1_subset_1(D_615, u1_struct_0('#skF_3')) | ~r2_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_513, C_514))) | ~m1_subset_1('#skF_1'('#skF_3', B_513, C_514), u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~r2_hidden('#skF_1'('#skF_3', B_513, C_514), '#skF_5') | r1_lattice3('#skF_3', B_513, C_514) | ~m1_subset_1(C_514, u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1882, c_2221])).
% 9.04/3.06  tff(c_3586, plain, (![D_932, B_933, C_934]: (r1_orders_2('#skF_3', D_932, k2_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_933, C_934)))) | ~r1_lattice3('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_933, C_934)), D_932) | ~m1_subset_1(D_932, u1_struct_0('#skF_3')) | ~r2_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_933, C_934))) | ~m1_subset_1('#skF_1'('#skF_3', B_933, C_934), u1_struct_0('#skF_3')) | ~r2_hidden('#skF_1'('#skF_3', B_933, C_934), '#skF_5') | r1_lattice3('#skF_3', B_933, C_934) | ~m1_subset_1(C_934, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2223])).
% 9.04/3.06  tff(c_4993, plain, (![D_1326, B_1327, C_1328]: (r1_orders_2('#skF_3', D_1326, '#skF_1'('#skF_3', B_1327, C_1328)) | ~r1_lattice3('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_1327, C_1328)), D_1326) | ~m1_subset_1(D_1326, u1_struct_0('#skF_3')) | ~r2_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_1327, C_1328))) | ~m1_subset_1('#skF_1'('#skF_3', B_1327, C_1328), u1_struct_0('#skF_3')) | ~r2_hidden('#skF_1'('#skF_3', B_1327, C_1328), '#skF_5') | r1_lattice3('#skF_3', B_1327, C_1328) | ~m1_subset_1(C_1328, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_1'('#skF_3', B_1327, C_1328), '#skF_5') | r1_lattice3('#skF_3', B_1327, C_1328) | ~m1_subset_1(C_1328, u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1882, c_3586])).
% 9.04/3.06  tff(c_5035, plain, (![B_1327, C_1328]: (r1_orders_2('#skF_3', '#skF_7', '#skF_1'('#skF_3', B_1327, C_1328)) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~r2_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_1327, C_1328))) | ~m1_subset_1('#skF_1'('#skF_3', B_1327, C_1328), u1_struct_0('#skF_3')) | ~r2_hidden('#skF_1'('#skF_3', B_1327, C_1328), '#skF_5') | r1_lattice3('#skF_3', B_1327, C_1328) | ~m1_subset_1(C_1328, u1_struct_0('#skF_3')) | ~r1_tarski('#skF_6'('#skF_1'('#skF_3', B_1327, C_1328)), '#skF_4'))), inference(resolution, [status(thm)], [c_1829, c_4993])).
% 9.04/3.06  tff(c_5065, plain, (![B_1329, C_1330]: (r1_orders_2('#skF_3', '#skF_7', '#skF_1'('#skF_3', B_1329, C_1330)) | ~r2_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_1329, C_1330))) | ~m1_subset_1('#skF_1'('#skF_3', B_1329, C_1330), u1_struct_0('#skF_3')) | ~r2_hidden('#skF_1'('#skF_3', B_1329, C_1330), '#skF_5') | r1_lattice3('#skF_3', B_1329, C_1330) | ~m1_subset_1(C_1330, u1_struct_0('#skF_3')) | ~r1_tarski('#skF_6'('#skF_1'('#skF_3', B_1329, C_1330)), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_5035])).
% 9.04/3.06  tff(c_5074, plain, (![B_1331, C_1332]: (r1_orders_2('#skF_3', '#skF_7', '#skF_1'('#skF_3', B_1331, C_1332)) | r1_lattice3('#skF_3', B_1331, C_1332) | ~m1_subset_1(C_1332, u1_struct_0('#skF_3')) | ~r1_tarski('#skF_6'('#skF_1'('#skF_3', B_1331, C_1332)), '#skF_4') | ~r2_hidden('#skF_1'('#skF_3', B_1331, C_1332), '#skF_5') | ~m1_subset_1('#skF_1'('#skF_3', B_1331, C_1332), u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_78, c_5065])).
% 9.04/3.06  tff(c_5079, plain, (![B_1333, C_1334]: (r1_orders_2('#skF_3', '#skF_7', '#skF_1'('#skF_3', B_1333, C_1334)) | r1_lattice3('#skF_3', B_1333, C_1334) | ~m1_subset_1(C_1334, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_1'('#skF_3', B_1333, C_1334), '#skF_5') | ~m1_subset_1('#skF_1'('#skF_3', B_1333, C_1334), u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_1820, c_5074])).
% 9.04/3.06  tff(c_5083, plain, (![B_20, C_21]: (r1_orders_2('#skF_3', '#skF_7', '#skF_1'('#skF_3', B_20, C_21)) | ~r2_hidden('#skF_1'('#skF_3', B_20, C_21), '#skF_5') | r1_lattice3('#skF_3', B_20, C_21) | ~m1_subset_1(C_21, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_26, c_5079])).
% 9.04/3.06  tff(c_5087, plain, (![B_1335, C_1336]: (r1_orders_2('#skF_3', '#skF_7', '#skF_1'('#skF_3', B_1335, C_1336)) | ~r2_hidden('#skF_1'('#skF_3', B_1335, C_1336), '#skF_5') | r1_lattice3('#skF_3', B_1335, C_1336) | ~m1_subset_1(C_1336, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_5083])).
% 9.04/3.06  tff(c_5095, plain, (![B_1335]: (~l1_orders_2('#skF_3') | ~r2_hidden('#skF_1'('#skF_3', B_1335, '#skF_7'), '#skF_5') | r1_lattice3('#skF_3', B_1335, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_5087, c_22])).
% 9.04/3.06  tff(c_5105, plain, (![B_1337]: (~r2_hidden('#skF_1'('#skF_3', B_1337, '#skF_7'), '#skF_5') | r1_lattice3('#skF_3', B_1337, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_60, c_5095])).
% 9.04/3.06  tff(c_5113, plain, (r1_lattice3('#skF_3', '#skF_5', '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_24, c_5105])).
% 9.04/3.06  tff(c_5119, plain, (r1_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_5113])).
% 9.04/3.06  tff(c_5121, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1776, c_5119])).
% 9.04/3.06  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.04/3.06  
% 9.04/3.06  Inference rules
% 9.04/3.06  ----------------------
% 9.04/3.06  #Ref     : 0
% 9.04/3.06  #Sup     : 985
% 9.04/3.06  #Fact    : 0
% 9.04/3.06  #Define  : 0
% 9.04/3.06  #Split   : 15
% 9.04/3.06  #Chain   : 0
% 9.04/3.06  #Close   : 0
% 9.04/3.06  
% 9.04/3.06  Ordering : KBO
% 9.04/3.06  
% 9.04/3.06  Simplification rules
% 9.04/3.06  ----------------------
% 9.04/3.06  #Subsume      : 249
% 9.04/3.06  #Demod        : 656
% 9.04/3.06  #Tautology    : 53
% 9.04/3.06  #SimpNegUnit  : 93
% 9.04/3.06  #BackRed      : 0
% 9.04/3.06  
% 9.04/3.06  #Partial instantiations: 0
% 9.04/3.06  #Strategies tried      : 1
% 9.04/3.06  
% 9.04/3.06  Timing (in seconds)
% 9.04/3.06  ----------------------
% 9.04/3.06  Preprocessing        : 0.36
% 9.04/3.06  Parsing              : 0.19
% 9.04/3.06  CNF conversion       : 0.03
% 9.04/3.06  Main loop            : 1.91
% 9.04/3.06  Inferencing          : 0.71
% 9.04/3.06  Reduction            : 0.53
% 9.04/3.06  Demodulation         : 0.34
% 9.04/3.06  BG Simplification    : 0.06
% 9.04/3.06  Subsumption          : 0.48
% 9.04/3.06  Abstraction          : 0.08
% 9.04/3.06  MUC search           : 0.00
% 9.04/3.06  Cooper               : 0.00
% 9.04/3.06  Total                : 2.32
% 9.04/3.06  Index Insertion      : 0.00
% 9.04/3.06  Index Deletion       : 0.00
% 9.04/3.06  Index Matching       : 0.00
% 9.04/3.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
