%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:01 EST 2020

% Result     : Theorem 7.58s
% Output     : CNFRefutation 7.58s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 231 expanded)
%              Number of leaves         :   40 (  98 expanded)
%              Depth                    :   20
%              Number of atoms          :  366 (1412 expanded)
%              Number of equality atoms :   35 ( 154 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_finset_1 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff(f_188,negated_conjecture,(
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

tff(f_71,axiom,(
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
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_45,axiom,(
    ! [A] : v1_finset_1(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_finset_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_57,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r1_orders_2(A,B,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_orders_2)).

tff(f_113,axiom,(
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

tff(f_89,axiom,(
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

tff(f_129,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_105,plain,(
    r2_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_68,plain,
    ( ~ r2_lattice3('#skF_3','#skF_5','#skF_7')
    | ~ r2_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_107,plain,(
    ~ r2_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_68])).

tff(c_60,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_50,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_24,plain,(
    ! [A_13,B_20,C_21] :
      ( r2_hidden('#skF_1'(A_13,B_20,C_21),B_20)
      | r2_lattice3(A_13,B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0(A_13))
      | ~ l1_orders_2(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

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

tff(c_16,plain,(
    ! [A_9] : v1_finset_1(k1_tarski(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_114,plain,(
    ! [A_114,C_115,B_116] :
      ( m1_subset_1(A_114,C_115)
      | ~ m1_subset_1(B_116,k1_zfmisc_1(C_115))
      | ~ r2_hidden(A_114,B_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_122,plain,(
    ! [A_114] :
      ( m1_subset_1(A_114,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_114,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_58,c_114])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_64,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_186,plain,(
    ! [A_131,B_132] :
      ( r1_orders_2(A_131,B_132,B_132)
      | ~ m1_subset_1(B_132,u1_struct_0(A_131))
      | ~ l1_orders_2(A_131)
      | ~ v3_orders_2(A_131)
      | v2_struct_0(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_190,plain,(
    ! [A_114] :
      ( r1_orders_2('#skF_3',A_114,A_114)
      | ~ l1_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r2_hidden(A_114,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_122,c_186])).

tff(c_199,plain,(
    ! [A_114] :
      ( r1_orders_2('#skF_3',A_114,A_114)
      | v2_struct_0('#skF_3')
      | ~ r2_hidden(A_114,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_190])).

tff(c_200,plain,(
    ! [A_114] :
      ( r1_orders_2('#skF_3',A_114,A_114)
      | ~ r2_hidden(A_114,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_199])).

tff(c_137,plain,(
    ! [D_124] :
      ( r1_yellow_0('#skF_3',D_124)
      | k1_xboole_0 = D_124
      | ~ m1_subset_1(D_124,k1_zfmisc_1('#skF_4'))
      | ~ v1_finset_1(D_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_142,plain,(
    ! [A_4] :
      ( r1_yellow_0('#skF_3',A_4)
      | k1_xboole_0 = A_4
      | ~ v1_finset_1(A_4)
      | ~ r1_tarski(A_4,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_12,c_137])).

tff(c_38,plain,(
    ! [A_37,C_43,B_41] :
      ( r2_lattice3(A_37,k1_tarski(C_43),B_41)
      | ~ r1_orders_2(A_37,C_43,B_41)
      | ~ m1_subset_1(C_43,u1_struct_0(A_37))
      | ~ m1_subset_1(B_41,u1_struct_0(A_37))
      | ~ l1_orders_2(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_32,plain,(
    ! [A_25,B_32,C_33] :
      ( m1_subset_1('#skF_2'(A_25,B_32,C_33),u1_struct_0(A_25))
      | k1_yellow_0(A_25,B_32) = C_33
      | ~ r2_lattice3(A_25,B_32,C_33)
      | ~ r1_yellow_0(A_25,B_32)
      | ~ m1_subset_1(C_33,u1_struct_0(A_25))
      | ~ l1_orders_2(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_612,plain,(
    ! [A_228,B_229,C_230] :
      ( r2_lattice3(A_228,B_229,'#skF_2'(A_228,B_229,C_230))
      | k1_yellow_0(A_228,B_229) = C_230
      | ~ r2_lattice3(A_228,B_229,C_230)
      | ~ r1_yellow_0(A_228,B_229)
      | ~ m1_subset_1(C_230,u1_struct_0(A_228))
      | ~ l1_orders_2(A_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_40,plain,(
    ! [A_37,C_43,B_41] :
      ( r1_orders_2(A_37,C_43,B_41)
      | ~ r2_lattice3(A_37,k1_tarski(C_43),B_41)
      | ~ m1_subset_1(C_43,u1_struct_0(A_37))
      | ~ m1_subset_1(B_41,u1_struct_0(A_37))
      | ~ l1_orders_2(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1344,plain,(
    ! [A_401,C_402,C_403] :
      ( r1_orders_2(A_401,C_402,'#skF_2'(A_401,k1_tarski(C_402),C_403))
      | ~ m1_subset_1(C_402,u1_struct_0(A_401))
      | ~ m1_subset_1('#skF_2'(A_401,k1_tarski(C_402),C_403),u1_struct_0(A_401))
      | k1_yellow_0(A_401,k1_tarski(C_402)) = C_403
      | ~ r2_lattice3(A_401,k1_tarski(C_402),C_403)
      | ~ r1_yellow_0(A_401,k1_tarski(C_402))
      | ~ m1_subset_1(C_403,u1_struct_0(A_401))
      | ~ l1_orders_2(A_401) ) ),
    inference(resolution,[status(thm)],[c_612,c_40])).

tff(c_2272,plain,(
    ! [A_516,C_517,C_518] :
      ( r1_orders_2(A_516,C_517,'#skF_2'(A_516,k1_tarski(C_517),C_518))
      | ~ m1_subset_1(C_517,u1_struct_0(A_516))
      | k1_yellow_0(A_516,k1_tarski(C_517)) = C_518
      | ~ r2_lattice3(A_516,k1_tarski(C_517),C_518)
      | ~ r1_yellow_0(A_516,k1_tarski(C_517))
      | ~ m1_subset_1(C_518,u1_struct_0(A_516))
      | ~ l1_orders_2(A_516) ) ),
    inference(resolution,[status(thm)],[c_32,c_1344])).

tff(c_28,plain,(
    ! [A_25,C_33,B_32] :
      ( ~ r1_orders_2(A_25,C_33,'#skF_2'(A_25,B_32,C_33))
      | k1_yellow_0(A_25,B_32) = C_33
      | ~ r2_lattice3(A_25,B_32,C_33)
      | ~ r1_yellow_0(A_25,B_32)
      | ~ m1_subset_1(C_33,u1_struct_0(A_25))
      | ~ l1_orders_2(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2288,plain,(
    ! [A_519,C_520] :
      ( k1_yellow_0(A_519,k1_tarski(C_520)) = C_520
      | ~ r2_lattice3(A_519,k1_tarski(C_520),C_520)
      | ~ r1_yellow_0(A_519,k1_tarski(C_520))
      | ~ m1_subset_1(C_520,u1_struct_0(A_519))
      | ~ l1_orders_2(A_519) ) ),
    inference(resolution,[status(thm)],[c_2272,c_28])).

tff(c_2426,plain,(
    ! [A_523,B_524] :
      ( k1_yellow_0(A_523,k1_tarski(B_524)) = B_524
      | ~ r1_yellow_0(A_523,k1_tarski(B_524))
      | ~ r1_orders_2(A_523,B_524,B_524)
      | ~ m1_subset_1(B_524,u1_struct_0(A_523))
      | ~ l1_orders_2(A_523) ) ),
    inference(resolution,[status(thm)],[c_38,c_2288])).

tff(c_2429,plain,(
    ! [B_524] :
      ( k1_yellow_0('#skF_3',k1_tarski(B_524)) = B_524
      | ~ r1_orders_2('#skF_3',B_524,B_524)
      | ~ m1_subset_1(B_524,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | k1_tarski(B_524) = k1_xboole_0
      | ~ v1_finset_1(k1_tarski(B_524))
      | ~ r1_tarski(k1_tarski(B_524),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_142,c_2426])).

tff(c_2450,plain,(
    ! [B_530] :
      ( k1_yellow_0('#skF_3',k1_tarski(B_530)) = B_530
      | ~ r1_orders_2('#skF_3',B_530,B_530)
      | ~ m1_subset_1(B_530,u1_struct_0('#skF_3'))
      | k1_tarski(B_530) = k1_xboole_0
      | ~ r1_tarski(k1_tarski(B_530),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_60,c_2429])).

tff(c_2533,plain,(
    ! [A_531] :
      ( k1_yellow_0('#skF_3',k1_tarski(A_531)) = A_531
      | ~ m1_subset_1(A_531,u1_struct_0('#skF_3'))
      | k1_tarski(A_531) = k1_xboole_0
      | ~ r1_tarski(k1_tarski(A_531),'#skF_4')
      | ~ r2_hidden(A_531,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_200,c_2450])).

tff(c_2539,plain,(
    ! [A_532] :
      ( k1_yellow_0('#skF_3',k1_tarski(A_532)) = A_532
      | ~ m1_subset_1(A_532,u1_struct_0('#skF_3'))
      | k1_tarski(A_532) = k1_xboole_0
      | ~ r2_hidden(A_532,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_8,c_2533])).

tff(c_2597,plain,(
    ! [A_535] :
      ( k1_yellow_0('#skF_3',k1_tarski(A_535)) = A_535
      | k1_tarski(A_535) = k1_xboole_0
      | ~ r2_hidden(A_535,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_122,c_2539])).

tff(c_52,plain,(
    ! [D_102] :
      ( r2_hidden(k1_yellow_0('#skF_3',D_102),'#skF_5')
      | k1_xboole_0 = D_102
      | ~ m1_subset_1(D_102,k1_zfmisc_1('#skF_4'))
      | ~ v1_finset_1(D_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_2677,plain,(
    ! [A_535] :
      ( r2_hidden(A_535,'#skF_5')
      | k1_tarski(A_535) = k1_xboole_0
      | ~ m1_subset_1(k1_tarski(A_535),k1_zfmisc_1('#skF_4'))
      | ~ v1_finset_1(k1_tarski(A_535))
      | k1_tarski(A_535) = k1_xboole_0
      | ~ r2_hidden(A_535,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2597,c_52])).

tff(c_2713,plain,(
    ! [A_536] :
      ( r2_hidden(A_536,'#skF_5')
      | ~ m1_subset_1(k1_tarski(A_536),k1_zfmisc_1('#skF_4'))
      | k1_tarski(A_536) = k1_xboole_0
      | ~ r2_hidden(A_536,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_2677])).

tff(c_2731,plain,(
    ! [A_538] :
      ( r2_hidden(A_538,'#skF_5')
      | k1_tarski(A_538) = k1_xboole_0
      | ~ r2_hidden(A_538,'#skF_4')
      | ~ r1_tarski(k1_tarski(A_538),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_12,c_2713])).

tff(c_2737,plain,(
    ! [A_539] :
      ( r2_hidden(A_539,'#skF_5')
      | k1_tarski(A_539) = k1_xboole_0
      | ~ r2_hidden(A_539,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_8,c_2731])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_123,plain,(
    ! [A_114] :
      ( m1_subset_1(A_114,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_114,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_56,c_114])).

tff(c_245,plain,(
    ! [A_152,B_153,D_154,C_155] :
      ( r2_lattice3(A_152,B_153,D_154)
      | ~ r2_lattice3(A_152,C_155,D_154)
      | ~ m1_subset_1(D_154,u1_struct_0(A_152))
      | ~ r1_tarski(B_153,C_155)
      | ~ l1_orders_2(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_247,plain,(
    ! [B_153] :
      ( r2_lattice3('#skF_3',B_153,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ r1_tarski(B_153,'#skF_5')
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_105,c_245])).

tff(c_250,plain,(
    ! [B_153] :
      ( r2_lattice3('#skF_3',B_153,'#skF_7')
      | ~ r1_tarski(B_153,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_247])).

tff(c_359,plain,(
    ! [A_171,C_172,B_173] :
      ( r1_orders_2(A_171,C_172,B_173)
      | ~ r2_lattice3(A_171,k1_tarski(C_172),B_173)
      | ~ m1_subset_1(C_172,u1_struct_0(A_171))
      | ~ m1_subset_1(B_173,u1_struct_0(A_171))
      | ~ l1_orders_2(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_375,plain,(
    ! [C_172] :
      ( r1_orders_2('#skF_3',C_172,'#skF_7')
      | ~ m1_subset_1(C_172,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ r1_tarski(k1_tarski(C_172),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_250,c_359])).

tff(c_388,plain,(
    ! [C_174] :
      ( r1_orders_2('#skF_3',C_174,'#skF_7')
      | ~ m1_subset_1(C_174,u1_struct_0('#skF_3'))
      | ~ r1_tarski(k1_tarski(C_174),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_375])).

tff(c_394,plain,(
    ! [A_175] :
      ( r1_orders_2('#skF_3',A_175,'#skF_7')
      | ~ m1_subset_1(A_175,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_175,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_8,c_388])).

tff(c_422,plain,(
    ! [A_176] :
      ( r1_orders_2('#skF_3',A_176,'#skF_7')
      | ~ r2_hidden(A_176,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_123,c_394])).

tff(c_22,plain,(
    ! [A_13,B_20,C_21] :
      ( ~ r1_orders_2(A_13,'#skF_1'(A_13,B_20,C_21),C_21)
      | r2_lattice3(A_13,B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0(A_13))
      | ~ l1_orders_2(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_426,plain,(
    ! [B_20] :
      ( r2_lattice3('#skF_3',B_20,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ r2_hidden('#skF_1'('#skF_3',B_20,'#skF_7'),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_422,c_22])).

tff(c_429,plain,(
    ! [B_20] :
      ( r2_lattice3('#skF_3',B_20,'#skF_7')
      | ~ r2_hidden('#skF_1'('#skF_3',B_20,'#skF_7'),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_426])).

tff(c_2796,plain,(
    ! [B_543] :
      ( r2_lattice3('#skF_3',B_543,'#skF_7')
      | k1_tarski('#skF_1'('#skF_3',B_543,'#skF_7')) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_543,'#skF_7'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2737,c_429])).

tff(c_2800,plain,
    ( k1_tarski('#skF_1'('#skF_3','#skF_4','#skF_7')) = k1_xboole_0
    | r2_lattice3('#skF_3','#skF_4','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_2796])).

tff(c_2803,plain,
    ( k1_tarski('#skF_1'('#skF_3','#skF_4','#skF_7')) = k1_xboole_0
    | r2_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_2800])).

tff(c_2804,plain,(
    k1_tarski('#skF_1'('#skF_3','#skF_4','#skF_7')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_2803])).

tff(c_4,plain,(
    ! [A_1] : ~ v1_xboole_0(k1_tarski(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2949,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2804,c_4])).

tff(c_2974,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2949])).

tff(c_2975,plain,(
    r2_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_2978,plain,(
    ~ r2_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2975,c_68])).

tff(c_2979,plain,(
    ! [A_544,C_545,B_546] :
      ( m1_subset_1(A_544,C_545)
      | ~ m1_subset_1(B_546,k1_zfmisc_1(C_545))
      | ~ r2_hidden(A_544,B_546) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2988,plain,(
    ! [A_544] :
      ( m1_subset_1(A_544,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_544,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_56,c_2979])).

tff(c_3015,plain,(
    ! [D_557] :
      ( m1_subset_1('#skF_6'(D_557),k1_zfmisc_1('#skF_4'))
      | ~ r2_hidden(D_557,'#skF_5')
      | ~ m1_subset_1(D_557,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3026,plain,(
    ! [D_557] :
      ( r1_tarski('#skF_6'(D_557),'#skF_4')
      | ~ r2_hidden(D_557,'#skF_5')
      | ~ m1_subset_1(D_557,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_3015,c_10])).

tff(c_78,plain,(
    ! [D_100] :
      ( r1_yellow_0('#skF_3','#skF_6'(D_100))
      | ~ r2_hidden(D_100,'#skF_5')
      | ~ m1_subset_1(D_100,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_3027,plain,(
    ! [D_558] :
      ( k1_yellow_0('#skF_3','#skF_6'(D_558)) = D_558
      | ~ r2_hidden(D_558,'#skF_5')
      | ~ m1_subset_1(D_558,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_3037,plain,(
    ! [A_544] :
      ( k1_yellow_0('#skF_3','#skF_6'(A_544)) = A_544
      | ~ r2_hidden(A_544,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2988,c_3027])).

tff(c_3114,plain,(
    ! [A_576,B_577,D_578,C_579] :
      ( r2_lattice3(A_576,B_577,D_578)
      | ~ r2_lattice3(A_576,C_579,D_578)
      | ~ m1_subset_1(D_578,u1_struct_0(A_576))
      | ~ r1_tarski(B_577,C_579)
      | ~ l1_orders_2(A_576) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_3116,plain,(
    ! [B_577] :
      ( r2_lattice3('#skF_3',B_577,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ r1_tarski(B_577,'#skF_4')
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2975,c_3114])).

tff(c_3119,plain,(
    ! [B_577] :
      ( r2_lattice3('#skF_3',B_577,'#skF_7')
      | ~ r1_tarski(B_577,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_3116])).

tff(c_3616,plain,(
    ! [A_693,B_694,D_695] :
      ( r1_orders_2(A_693,k1_yellow_0(A_693,B_694),D_695)
      | ~ r2_lattice3(A_693,B_694,D_695)
      | ~ m1_subset_1(D_695,u1_struct_0(A_693))
      | ~ r1_yellow_0(A_693,B_694)
      | ~ m1_subset_1(k1_yellow_0(A_693,B_694),u1_struct_0(A_693))
      | ~ l1_orders_2(A_693) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_3624,plain,(
    ! [B_694,D_695] :
      ( r1_orders_2('#skF_3',k1_yellow_0('#skF_3',B_694),D_695)
      | ~ r2_lattice3('#skF_3',B_694,D_695)
      | ~ m1_subset_1(D_695,u1_struct_0('#skF_3'))
      | ~ r1_yellow_0('#skF_3',B_694)
      | ~ l1_orders_2('#skF_3')
      | ~ r2_hidden(k1_yellow_0('#skF_3',B_694),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2988,c_3616])).

tff(c_3750,plain,(
    ! [B_725,D_726] :
      ( r1_orders_2('#skF_3',k1_yellow_0('#skF_3',B_725),D_726)
      | ~ r2_lattice3('#skF_3',B_725,D_726)
      | ~ m1_subset_1(D_726,u1_struct_0('#skF_3'))
      | ~ r1_yellow_0('#skF_3',B_725)
      | ~ r2_hidden(k1_yellow_0('#skF_3',B_725),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_3624])).

tff(c_4135,plain,(
    ! [A_810,D_811] :
      ( r1_orders_2('#skF_3',A_810,D_811)
      | ~ r2_lattice3('#skF_3','#skF_6'(A_810),D_811)
      | ~ m1_subset_1(D_811,u1_struct_0('#skF_3'))
      | ~ r1_yellow_0('#skF_3','#skF_6'(A_810))
      | ~ r2_hidden(k1_yellow_0('#skF_3','#skF_6'(A_810)),'#skF_5')
      | ~ r2_hidden(A_810,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3037,c_3750])).

tff(c_4168,plain,(
    ! [A_810] :
      ( r1_orders_2('#skF_3',A_810,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ r1_yellow_0('#skF_3','#skF_6'(A_810))
      | ~ r2_hidden(k1_yellow_0('#skF_3','#skF_6'(A_810)),'#skF_5')
      | ~ r2_hidden(A_810,'#skF_5')
      | ~ r1_tarski('#skF_6'(A_810),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_3119,c_4135])).

tff(c_4186,plain,(
    ! [A_812] :
      ( r1_orders_2('#skF_3',A_812,'#skF_7')
      | ~ r1_yellow_0('#skF_3','#skF_6'(A_812))
      | ~ r2_hidden(k1_yellow_0('#skF_3','#skF_6'(A_812)),'#skF_5')
      | ~ r2_hidden(A_812,'#skF_5')
      | ~ r1_tarski('#skF_6'(A_812),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_4168])).

tff(c_4194,plain,(
    ! [A_813] :
      ( r1_orders_2('#skF_3',A_813,'#skF_7')
      | ~ r1_yellow_0('#skF_3','#skF_6'(A_813))
      | ~ r2_hidden(A_813,'#skF_5')
      | ~ r2_hidden(A_813,'#skF_5')
      | ~ r1_tarski('#skF_6'(A_813),'#skF_4')
      | ~ r2_hidden(A_813,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3037,c_4186])).

tff(c_4203,plain,(
    ! [D_814] :
      ( r1_orders_2('#skF_3',D_814,'#skF_7')
      | ~ r1_tarski('#skF_6'(D_814),'#skF_4')
      | ~ r2_hidden(D_814,'#skF_5')
      | ~ m1_subset_1(D_814,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_78,c_4194])).

tff(c_4208,plain,(
    ! [D_815] :
      ( r1_orders_2('#skF_3',D_815,'#skF_7')
      | ~ r2_hidden(D_815,'#skF_5')
      | ~ m1_subset_1(D_815,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_3026,c_4203])).

tff(c_4248,plain,(
    ! [A_816] :
      ( r1_orders_2('#skF_3',A_816,'#skF_7')
      | ~ r2_hidden(A_816,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2988,c_4208])).

tff(c_4256,plain,(
    ! [B_20] :
      ( r2_lattice3('#skF_3',B_20,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ r2_hidden('#skF_1'('#skF_3',B_20,'#skF_7'),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_4248,c_22])).

tff(c_4283,plain,(
    ! [B_821] :
      ( r2_lattice3('#skF_3',B_821,'#skF_7')
      | ~ r2_hidden('#skF_1'('#skF_3',B_821,'#skF_7'),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_4256])).

tff(c_4287,plain,
    ( r2_lattice3('#skF_3','#skF_5','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_4283])).

tff(c_4290,plain,(
    r2_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_4287])).

tff(c_4292,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2978,c_4290])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:51:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.58/2.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.58/2.63  
% 7.58/2.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.58/2.63  %$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_finset_1 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_6
% 7.58/2.63  
% 7.58/2.63  %Foreground sorts:
% 7.58/2.63  
% 7.58/2.63  
% 7.58/2.63  %Background operators:
% 7.58/2.63  
% 7.58/2.63  
% 7.58/2.63  %Foreground operators:
% 7.58/2.63  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.58/2.63  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 7.58/2.63  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.58/2.63  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 7.58/2.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.58/2.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.58/2.63  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.58/2.63  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 7.58/2.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.58/2.63  tff('#skF_7', type, '#skF_7': $i).
% 7.58/2.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.58/2.63  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 7.58/2.63  tff('#skF_5', type, '#skF_5': $i).
% 7.58/2.63  tff('#skF_3', type, '#skF_3': $i).
% 7.58/2.64  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.58/2.64  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 7.58/2.64  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 7.58/2.64  tff(r1_yellow_0, type, r1_yellow_0: ($i * $i) > $o).
% 7.58/2.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.58/2.64  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 7.58/2.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.58/2.64  tff('#skF_4', type, '#skF_4': $i).
% 7.58/2.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.58/2.64  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.58/2.64  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.58/2.64  tff(v1_finset_1, type, v1_finset_1: $i > $o).
% 7.58/2.64  tff('#skF_6', type, '#skF_6': $i > $i).
% 7.58/2.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.58/2.64  
% 7.58/2.67  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.58/2.67  tff(f_188, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((((![D]: ((v1_finset_1(D) & m1_subset_1(D, k1_zfmisc_1(B))) => (~(D = k1_xboole_0) => r1_yellow_0(A, D)))) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => ~(r2_hidden(D, C) & (![E]: ((v1_finset_1(E) & m1_subset_1(E, k1_zfmisc_1(B))) => ~(r1_yellow_0(A, E) & (D = k1_yellow_0(A, E))))))))) & (![D]: ((v1_finset_1(D) & m1_subset_1(D, k1_zfmisc_1(B))) => (~(D = k1_xboole_0) => r2_hidden(k1_yellow_0(A, D), C))))) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, B, D) <=> r2_lattice3(A, C, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_waybel_0)).
% 7.58/2.67  tff(f_71, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, D, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_lattice3)).
% 7.58/2.67  tff(f_33, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 7.58/2.67  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.58/2.67  tff(f_45, axiom, (![A]: v1_finset_1(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_finset_1)).
% 7.58/2.67  tff(f_43, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 7.58/2.67  tff(f_57, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, B, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_orders_2)).
% 7.58/2.67  tff(f_113, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((((r1_lattice3(A, k1_tarski(C), B) => r1_orders_2(A, B, C)) & (r1_orders_2(A, B, C) => r1_lattice3(A, k1_tarski(C), B))) & (r2_lattice3(A, k1_tarski(C), B) => r1_orders_2(A, C, B))) & (r1_orders_2(A, C, B) => r2_lattice3(A, k1_tarski(C), B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_yellow_0)).
% 7.58/2.67  tff(f_89, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_yellow_0(A, B) => ((C = k1_yellow_0(A, B)) <=> (r2_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, B, D) => r1_orders_2(A, C, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_yellow_0)).
% 7.58/2.67  tff(f_129, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (r1_tarski(B, C) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r1_lattice3(A, C, D) => r1_lattice3(A, B, D)) & (r2_lattice3(A, C, D) => r2_lattice3(A, B, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_yellow_0)).
% 7.58/2.67  tff(f_29, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 7.58/2.67  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 7.58/2.67  tff(c_74, plain, (r2_lattice3('#skF_3', '#skF_4', '#skF_7') | r2_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_188])).
% 7.58/2.67  tff(c_105, plain, (r2_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(splitLeft, [status(thm)], [c_74])).
% 7.58/2.67  tff(c_68, plain, (~r2_lattice3('#skF_3', '#skF_5', '#skF_7') | ~r2_lattice3('#skF_3', '#skF_4', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_188])).
% 7.58/2.67  tff(c_107, plain, (~r2_lattice3('#skF_3', '#skF_4', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_68])).
% 7.58/2.67  tff(c_60, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_188])).
% 7.58/2.67  tff(c_50, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_188])).
% 7.58/2.67  tff(c_24, plain, (![A_13, B_20, C_21]: (r2_hidden('#skF_1'(A_13, B_20, C_21), B_20) | r2_lattice3(A_13, B_20, C_21) | ~m1_subset_1(C_21, u1_struct_0(A_13)) | ~l1_orders_2(A_13))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.58/2.67  tff(c_8, plain, (![A_2, B_3]: (r1_tarski(k1_tarski(A_2), B_3) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.58/2.67  tff(c_12, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.58/2.67  tff(c_16, plain, (![A_9]: (v1_finset_1(k1_tarski(A_9)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.58/2.67  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_188])).
% 7.58/2.67  tff(c_114, plain, (![A_114, C_115, B_116]: (m1_subset_1(A_114, C_115) | ~m1_subset_1(B_116, k1_zfmisc_1(C_115)) | ~r2_hidden(A_114, B_116))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.58/2.67  tff(c_122, plain, (![A_114]: (m1_subset_1(A_114, u1_struct_0('#skF_3')) | ~r2_hidden(A_114, '#skF_4'))), inference(resolution, [status(thm)], [c_58, c_114])).
% 7.58/2.67  tff(c_66, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_188])).
% 7.58/2.67  tff(c_64, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_188])).
% 7.58/2.67  tff(c_186, plain, (![A_131, B_132]: (r1_orders_2(A_131, B_132, B_132) | ~m1_subset_1(B_132, u1_struct_0(A_131)) | ~l1_orders_2(A_131) | ~v3_orders_2(A_131) | v2_struct_0(A_131))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.58/2.67  tff(c_190, plain, (![A_114]: (r1_orders_2('#skF_3', A_114, A_114) | ~l1_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3') | ~r2_hidden(A_114, '#skF_4'))), inference(resolution, [status(thm)], [c_122, c_186])).
% 7.58/2.67  tff(c_199, plain, (![A_114]: (r1_orders_2('#skF_3', A_114, A_114) | v2_struct_0('#skF_3') | ~r2_hidden(A_114, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_190])).
% 7.58/2.67  tff(c_200, plain, (![A_114]: (r1_orders_2('#skF_3', A_114, A_114) | ~r2_hidden(A_114, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_66, c_199])).
% 7.58/2.67  tff(c_137, plain, (![D_124]: (r1_yellow_0('#skF_3', D_124) | k1_xboole_0=D_124 | ~m1_subset_1(D_124, k1_zfmisc_1('#skF_4')) | ~v1_finset_1(D_124))), inference(cnfTransformation, [status(thm)], [f_188])).
% 7.58/2.67  tff(c_142, plain, (![A_4]: (r1_yellow_0('#skF_3', A_4) | k1_xboole_0=A_4 | ~v1_finset_1(A_4) | ~r1_tarski(A_4, '#skF_4'))), inference(resolution, [status(thm)], [c_12, c_137])).
% 7.58/2.67  tff(c_38, plain, (![A_37, C_43, B_41]: (r2_lattice3(A_37, k1_tarski(C_43), B_41) | ~r1_orders_2(A_37, C_43, B_41) | ~m1_subset_1(C_43, u1_struct_0(A_37)) | ~m1_subset_1(B_41, u1_struct_0(A_37)) | ~l1_orders_2(A_37))), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.58/2.67  tff(c_32, plain, (![A_25, B_32, C_33]: (m1_subset_1('#skF_2'(A_25, B_32, C_33), u1_struct_0(A_25)) | k1_yellow_0(A_25, B_32)=C_33 | ~r2_lattice3(A_25, B_32, C_33) | ~r1_yellow_0(A_25, B_32) | ~m1_subset_1(C_33, u1_struct_0(A_25)) | ~l1_orders_2(A_25))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.58/2.67  tff(c_612, plain, (![A_228, B_229, C_230]: (r2_lattice3(A_228, B_229, '#skF_2'(A_228, B_229, C_230)) | k1_yellow_0(A_228, B_229)=C_230 | ~r2_lattice3(A_228, B_229, C_230) | ~r1_yellow_0(A_228, B_229) | ~m1_subset_1(C_230, u1_struct_0(A_228)) | ~l1_orders_2(A_228))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.58/2.67  tff(c_40, plain, (![A_37, C_43, B_41]: (r1_orders_2(A_37, C_43, B_41) | ~r2_lattice3(A_37, k1_tarski(C_43), B_41) | ~m1_subset_1(C_43, u1_struct_0(A_37)) | ~m1_subset_1(B_41, u1_struct_0(A_37)) | ~l1_orders_2(A_37))), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.58/2.67  tff(c_1344, plain, (![A_401, C_402, C_403]: (r1_orders_2(A_401, C_402, '#skF_2'(A_401, k1_tarski(C_402), C_403)) | ~m1_subset_1(C_402, u1_struct_0(A_401)) | ~m1_subset_1('#skF_2'(A_401, k1_tarski(C_402), C_403), u1_struct_0(A_401)) | k1_yellow_0(A_401, k1_tarski(C_402))=C_403 | ~r2_lattice3(A_401, k1_tarski(C_402), C_403) | ~r1_yellow_0(A_401, k1_tarski(C_402)) | ~m1_subset_1(C_403, u1_struct_0(A_401)) | ~l1_orders_2(A_401))), inference(resolution, [status(thm)], [c_612, c_40])).
% 7.58/2.67  tff(c_2272, plain, (![A_516, C_517, C_518]: (r1_orders_2(A_516, C_517, '#skF_2'(A_516, k1_tarski(C_517), C_518)) | ~m1_subset_1(C_517, u1_struct_0(A_516)) | k1_yellow_0(A_516, k1_tarski(C_517))=C_518 | ~r2_lattice3(A_516, k1_tarski(C_517), C_518) | ~r1_yellow_0(A_516, k1_tarski(C_517)) | ~m1_subset_1(C_518, u1_struct_0(A_516)) | ~l1_orders_2(A_516))), inference(resolution, [status(thm)], [c_32, c_1344])).
% 7.58/2.67  tff(c_28, plain, (![A_25, C_33, B_32]: (~r1_orders_2(A_25, C_33, '#skF_2'(A_25, B_32, C_33)) | k1_yellow_0(A_25, B_32)=C_33 | ~r2_lattice3(A_25, B_32, C_33) | ~r1_yellow_0(A_25, B_32) | ~m1_subset_1(C_33, u1_struct_0(A_25)) | ~l1_orders_2(A_25))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.58/2.67  tff(c_2288, plain, (![A_519, C_520]: (k1_yellow_0(A_519, k1_tarski(C_520))=C_520 | ~r2_lattice3(A_519, k1_tarski(C_520), C_520) | ~r1_yellow_0(A_519, k1_tarski(C_520)) | ~m1_subset_1(C_520, u1_struct_0(A_519)) | ~l1_orders_2(A_519))), inference(resolution, [status(thm)], [c_2272, c_28])).
% 7.58/2.67  tff(c_2426, plain, (![A_523, B_524]: (k1_yellow_0(A_523, k1_tarski(B_524))=B_524 | ~r1_yellow_0(A_523, k1_tarski(B_524)) | ~r1_orders_2(A_523, B_524, B_524) | ~m1_subset_1(B_524, u1_struct_0(A_523)) | ~l1_orders_2(A_523))), inference(resolution, [status(thm)], [c_38, c_2288])).
% 7.58/2.67  tff(c_2429, plain, (![B_524]: (k1_yellow_0('#skF_3', k1_tarski(B_524))=B_524 | ~r1_orders_2('#skF_3', B_524, B_524) | ~m1_subset_1(B_524, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | k1_tarski(B_524)=k1_xboole_0 | ~v1_finset_1(k1_tarski(B_524)) | ~r1_tarski(k1_tarski(B_524), '#skF_4'))), inference(resolution, [status(thm)], [c_142, c_2426])).
% 7.58/2.67  tff(c_2450, plain, (![B_530]: (k1_yellow_0('#skF_3', k1_tarski(B_530))=B_530 | ~r1_orders_2('#skF_3', B_530, B_530) | ~m1_subset_1(B_530, u1_struct_0('#skF_3')) | k1_tarski(B_530)=k1_xboole_0 | ~r1_tarski(k1_tarski(B_530), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_60, c_2429])).
% 7.58/2.67  tff(c_2533, plain, (![A_531]: (k1_yellow_0('#skF_3', k1_tarski(A_531))=A_531 | ~m1_subset_1(A_531, u1_struct_0('#skF_3')) | k1_tarski(A_531)=k1_xboole_0 | ~r1_tarski(k1_tarski(A_531), '#skF_4') | ~r2_hidden(A_531, '#skF_4'))), inference(resolution, [status(thm)], [c_200, c_2450])).
% 7.58/2.67  tff(c_2539, plain, (![A_532]: (k1_yellow_0('#skF_3', k1_tarski(A_532))=A_532 | ~m1_subset_1(A_532, u1_struct_0('#skF_3')) | k1_tarski(A_532)=k1_xboole_0 | ~r2_hidden(A_532, '#skF_4'))), inference(resolution, [status(thm)], [c_8, c_2533])).
% 7.58/2.67  tff(c_2597, plain, (![A_535]: (k1_yellow_0('#skF_3', k1_tarski(A_535))=A_535 | k1_tarski(A_535)=k1_xboole_0 | ~r2_hidden(A_535, '#skF_4'))), inference(resolution, [status(thm)], [c_122, c_2539])).
% 7.58/2.67  tff(c_52, plain, (![D_102]: (r2_hidden(k1_yellow_0('#skF_3', D_102), '#skF_5') | k1_xboole_0=D_102 | ~m1_subset_1(D_102, k1_zfmisc_1('#skF_4')) | ~v1_finset_1(D_102))), inference(cnfTransformation, [status(thm)], [f_188])).
% 7.58/2.67  tff(c_2677, plain, (![A_535]: (r2_hidden(A_535, '#skF_5') | k1_tarski(A_535)=k1_xboole_0 | ~m1_subset_1(k1_tarski(A_535), k1_zfmisc_1('#skF_4')) | ~v1_finset_1(k1_tarski(A_535)) | k1_tarski(A_535)=k1_xboole_0 | ~r2_hidden(A_535, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2597, c_52])).
% 7.58/2.67  tff(c_2713, plain, (![A_536]: (r2_hidden(A_536, '#skF_5') | ~m1_subset_1(k1_tarski(A_536), k1_zfmisc_1('#skF_4')) | k1_tarski(A_536)=k1_xboole_0 | ~r2_hidden(A_536, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_2677])).
% 7.58/2.67  tff(c_2731, plain, (![A_538]: (r2_hidden(A_538, '#skF_5') | k1_tarski(A_538)=k1_xboole_0 | ~r2_hidden(A_538, '#skF_4') | ~r1_tarski(k1_tarski(A_538), '#skF_4'))), inference(resolution, [status(thm)], [c_12, c_2713])).
% 7.58/2.67  tff(c_2737, plain, (![A_539]: (r2_hidden(A_539, '#skF_5') | k1_tarski(A_539)=k1_xboole_0 | ~r2_hidden(A_539, '#skF_4'))), inference(resolution, [status(thm)], [c_8, c_2731])).
% 7.58/2.67  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_188])).
% 7.58/2.67  tff(c_123, plain, (![A_114]: (m1_subset_1(A_114, u1_struct_0('#skF_3')) | ~r2_hidden(A_114, '#skF_5'))), inference(resolution, [status(thm)], [c_56, c_114])).
% 7.58/2.67  tff(c_245, plain, (![A_152, B_153, D_154, C_155]: (r2_lattice3(A_152, B_153, D_154) | ~r2_lattice3(A_152, C_155, D_154) | ~m1_subset_1(D_154, u1_struct_0(A_152)) | ~r1_tarski(B_153, C_155) | ~l1_orders_2(A_152))), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.58/2.67  tff(c_247, plain, (![B_153]: (r2_lattice3('#skF_3', B_153, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~r1_tarski(B_153, '#skF_5') | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_105, c_245])).
% 7.58/2.67  tff(c_250, plain, (![B_153]: (r2_lattice3('#skF_3', B_153, '#skF_7') | ~r1_tarski(B_153, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_247])).
% 7.58/2.67  tff(c_359, plain, (![A_171, C_172, B_173]: (r1_orders_2(A_171, C_172, B_173) | ~r2_lattice3(A_171, k1_tarski(C_172), B_173) | ~m1_subset_1(C_172, u1_struct_0(A_171)) | ~m1_subset_1(B_173, u1_struct_0(A_171)) | ~l1_orders_2(A_171))), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.58/2.67  tff(c_375, plain, (![C_172]: (r1_orders_2('#skF_3', C_172, '#skF_7') | ~m1_subset_1(C_172, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~r1_tarski(k1_tarski(C_172), '#skF_5'))), inference(resolution, [status(thm)], [c_250, c_359])).
% 7.58/2.67  tff(c_388, plain, (![C_174]: (r1_orders_2('#skF_3', C_174, '#skF_7') | ~m1_subset_1(C_174, u1_struct_0('#skF_3')) | ~r1_tarski(k1_tarski(C_174), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_375])).
% 7.58/2.67  tff(c_394, plain, (![A_175]: (r1_orders_2('#skF_3', A_175, '#skF_7') | ~m1_subset_1(A_175, u1_struct_0('#skF_3')) | ~r2_hidden(A_175, '#skF_5'))), inference(resolution, [status(thm)], [c_8, c_388])).
% 7.58/2.67  tff(c_422, plain, (![A_176]: (r1_orders_2('#skF_3', A_176, '#skF_7') | ~r2_hidden(A_176, '#skF_5'))), inference(resolution, [status(thm)], [c_123, c_394])).
% 7.58/2.67  tff(c_22, plain, (![A_13, B_20, C_21]: (~r1_orders_2(A_13, '#skF_1'(A_13, B_20, C_21), C_21) | r2_lattice3(A_13, B_20, C_21) | ~m1_subset_1(C_21, u1_struct_0(A_13)) | ~l1_orders_2(A_13))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.58/2.67  tff(c_426, plain, (![B_20]: (r2_lattice3('#skF_3', B_20, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~r2_hidden('#skF_1'('#skF_3', B_20, '#skF_7'), '#skF_5'))), inference(resolution, [status(thm)], [c_422, c_22])).
% 7.58/2.67  tff(c_429, plain, (![B_20]: (r2_lattice3('#skF_3', B_20, '#skF_7') | ~r2_hidden('#skF_1'('#skF_3', B_20, '#skF_7'), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_426])).
% 7.58/2.67  tff(c_2796, plain, (![B_543]: (r2_lattice3('#skF_3', B_543, '#skF_7') | k1_tarski('#skF_1'('#skF_3', B_543, '#skF_7'))=k1_xboole_0 | ~r2_hidden('#skF_1'('#skF_3', B_543, '#skF_7'), '#skF_4'))), inference(resolution, [status(thm)], [c_2737, c_429])).
% 7.58/2.67  tff(c_2800, plain, (k1_tarski('#skF_1'('#skF_3', '#skF_4', '#skF_7'))=k1_xboole_0 | r2_lattice3('#skF_3', '#skF_4', '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_24, c_2796])).
% 7.58/2.67  tff(c_2803, plain, (k1_tarski('#skF_1'('#skF_3', '#skF_4', '#skF_7'))=k1_xboole_0 | r2_lattice3('#skF_3', '#skF_4', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_2800])).
% 7.58/2.67  tff(c_2804, plain, (k1_tarski('#skF_1'('#skF_3', '#skF_4', '#skF_7'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_107, c_2803])).
% 7.58/2.67  tff(c_4, plain, (![A_1]: (~v1_xboole_0(k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.58/2.67  tff(c_2949, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2804, c_4])).
% 7.58/2.67  tff(c_2974, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_2949])).
% 7.58/2.67  tff(c_2975, plain, (r2_lattice3('#skF_3', '#skF_4', '#skF_7')), inference(splitRight, [status(thm)], [c_74])).
% 7.58/2.67  tff(c_2978, plain, (~r2_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2975, c_68])).
% 7.58/2.67  tff(c_2979, plain, (![A_544, C_545, B_546]: (m1_subset_1(A_544, C_545) | ~m1_subset_1(B_546, k1_zfmisc_1(C_545)) | ~r2_hidden(A_544, B_546))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.58/2.67  tff(c_2988, plain, (![A_544]: (m1_subset_1(A_544, u1_struct_0('#skF_3')) | ~r2_hidden(A_544, '#skF_5'))), inference(resolution, [status(thm)], [c_56, c_2979])).
% 7.58/2.67  tff(c_3015, plain, (![D_557]: (m1_subset_1('#skF_6'(D_557), k1_zfmisc_1('#skF_4')) | ~r2_hidden(D_557, '#skF_5') | ~m1_subset_1(D_557, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_188])).
% 7.58/2.67  tff(c_10, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.58/2.67  tff(c_3026, plain, (![D_557]: (r1_tarski('#skF_6'(D_557), '#skF_4') | ~r2_hidden(D_557, '#skF_5') | ~m1_subset_1(D_557, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_3015, c_10])).
% 7.58/2.67  tff(c_78, plain, (![D_100]: (r1_yellow_0('#skF_3', '#skF_6'(D_100)) | ~r2_hidden(D_100, '#skF_5') | ~m1_subset_1(D_100, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_188])).
% 7.58/2.67  tff(c_3027, plain, (![D_558]: (k1_yellow_0('#skF_3', '#skF_6'(D_558))=D_558 | ~r2_hidden(D_558, '#skF_5') | ~m1_subset_1(D_558, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_188])).
% 7.58/2.67  tff(c_3037, plain, (![A_544]: (k1_yellow_0('#skF_3', '#skF_6'(A_544))=A_544 | ~r2_hidden(A_544, '#skF_5'))), inference(resolution, [status(thm)], [c_2988, c_3027])).
% 7.58/2.67  tff(c_3114, plain, (![A_576, B_577, D_578, C_579]: (r2_lattice3(A_576, B_577, D_578) | ~r2_lattice3(A_576, C_579, D_578) | ~m1_subset_1(D_578, u1_struct_0(A_576)) | ~r1_tarski(B_577, C_579) | ~l1_orders_2(A_576))), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.58/2.67  tff(c_3116, plain, (![B_577]: (r2_lattice3('#skF_3', B_577, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~r1_tarski(B_577, '#skF_4') | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_2975, c_3114])).
% 7.58/2.67  tff(c_3119, plain, (![B_577]: (r2_lattice3('#skF_3', B_577, '#skF_7') | ~r1_tarski(B_577, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_3116])).
% 7.58/2.67  tff(c_3616, plain, (![A_693, B_694, D_695]: (r1_orders_2(A_693, k1_yellow_0(A_693, B_694), D_695) | ~r2_lattice3(A_693, B_694, D_695) | ~m1_subset_1(D_695, u1_struct_0(A_693)) | ~r1_yellow_0(A_693, B_694) | ~m1_subset_1(k1_yellow_0(A_693, B_694), u1_struct_0(A_693)) | ~l1_orders_2(A_693))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.58/2.67  tff(c_3624, plain, (![B_694, D_695]: (r1_orders_2('#skF_3', k1_yellow_0('#skF_3', B_694), D_695) | ~r2_lattice3('#skF_3', B_694, D_695) | ~m1_subset_1(D_695, u1_struct_0('#skF_3')) | ~r1_yellow_0('#skF_3', B_694) | ~l1_orders_2('#skF_3') | ~r2_hidden(k1_yellow_0('#skF_3', B_694), '#skF_5'))), inference(resolution, [status(thm)], [c_2988, c_3616])).
% 7.58/2.67  tff(c_3750, plain, (![B_725, D_726]: (r1_orders_2('#skF_3', k1_yellow_0('#skF_3', B_725), D_726) | ~r2_lattice3('#skF_3', B_725, D_726) | ~m1_subset_1(D_726, u1_struct_0('#skF_3')) | ~r1_yellow_0('#skF_3', B_725) | ~r2_hidden(k1_yellow_0('#skF_3', B_725), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_3624])).
% 7.58/2.67  tff(c_4135, plain, (![A_810, D_811]: (r1_orders_2('#skF_3', A_810, D_811) | ~r2_lattice3('#skF_3', '#skF_6'(A_810), D_811) | ~m1_subset_1(D_811, u1_struct_0('#skF_3')) | ~r1_yellow_0('#skF_3', '#skF_6'(A_810)) | ~r2_hidden(k1_yellow_0('#skF_3', '#skF_6'(A_810)), '#skF_5') | ~r2_hidden(A_810, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3037, c_3750])).
% 7.58/2.67  tff(c_4168, plain, (![A_810]: (r1_orders_2('#skF_3', A_810, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~r1_yellow_0('#skF_3', '#skF_6'(A_810)) | ~r2_hidden(k1_yellow_0('#skF_3', '#skF_6'(A_810)), '#skF_5') | ~r2_hidden(A_810, '#skF_5') | ~r1_tarski('#skF_6'(A_810), '#skF_4'))), inference(resolution, [status(thm)], [c_3119, c_4135])).
% 7.58/2.67  tff(c_4186, plain, (![A_812]: (r1_orders_2('#skF_3', A_812, '#skF_7') | ~r1_yellow_0('#skF_3', '#skF_6'(A_812)) | ~r2_hidden(k1_yellow_0('#skF_3', '#skF_6'(A_812)), '#skF_5') | ~r2_hidden(A_812, '#skF_5') | ~r1_tarski('#skF_6'(A_812), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_4168])).
% 7.58/2.67  tff(c_4194, plain, (![A_813]: (r1_orders_2('#skF_3', A_813, '#skF_7') | ~r1_yellow_0('#skF_3', '#skF_6'(A_813)) | ~r2_hidden(A_813, '#skF_5') | ~r2_hidden(A_813, '#skF_5') | ~r1_tarski('#skF_6'(A_813), '#skF_4') | ~r2_hidden(A_813, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3037, c_4186])).
% 7.58/2.67  tff(c_4203, plain, (![D_814]: (r1_orders_2('#skF_3', D_814, '#skF_7') | ~r1_tarski('#skF_6'(D_814), '#skF_4') | ~r2_hidden(D_814, '#skF_5') | ~m1_subset_1(D_814, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_78, c_4194])).
% 7.58/2.67  tff(c_4208, plain, (![D_815]: (r1_orders_2('#skF_3', D_815, '#skF_7') | ~r2_hidden(D_815, '#skF_5') | ~m1_subset_1(D_815, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_3026, c_4203])).
% 7.58/2.67  tff(c_4248, plain, (![A_816]: (r1_orders_2('#skF_3', A_816, '#skF_7') | ~r2_hidden(A_816, '#skF_5'))), inference(resolution, [status(thm)], [c_2988, c_4208])).
% 7.58/2.67  tff(c_4256, plain, (![B_20]: (r2_lattice3('#skF_3', B_20, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~r2_hidden('#skF_1'('#skF_3', B_20, '#skF_7'), '#skF_5'))), inference(resolution, [status(thm)], [c_4248, c_22])).
% 7.58/2.67  tff(c_4283, plain, (![B_821]: (r2_lattice3('#skF_3', B_821, '#skF_7') | ~r2_hidden('#skF_1'('#skF_3', B_821, '#skF_7'), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_4256])).
% 7.58/2.67  tff(c_4287, plain, (r2_lattice3('#skF_3', '#skF_5', '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_24, c_4283])).
% 7.58/2.67  tff(c_4290, plain, (r2_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_4287])).
% 7.58/2.67  tff(c_4292, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2978, c_4290])).
% 7.58/2.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.58/2.67  
% 7.58/2.67  Inference rules
% 7.58/2.67  ----------------------
% 7.58/2.67  #Ref     : 0
% 7.58/2.67  #Sup     : 889
% 7.58/2.67  #Fact    : 0
% 7.58/2.67  #Define  : 0
% 7.58/2.67  #Split   : 24
% 7.58/2.67  #Chain   : 0
% 7.58/2.67  #Close   : 0
% 7.58/2.67  
% 7.58/2.67  Ordering : KBO
% 7.58/2.67  
% 7.58/2.67  Simplification rules
% 7.58/2.67  ----------------------
% 7.58/2.67  #Subsume      : 143
% 7.58/2.67  #Demod        : 394
% 7.58/2.67  #Tautology    : 29
% 7.58/2.67  #SimpNegUnit  : 16
% 7.58/2.67  #BackRed      : 0
% 7.58/2.67  
% 7.58/2.67  #Partial instantiations: 0
% 7.58/2.67  #Strategies tried      : 1
% 7.58/2.67  
% 7.58/2.67  Timing (in seconds)
% 7.58/2.67  ----------------------
% 7.58/2.68  Preprocessing        : 0.35
% 7.58/2.68  Parsing              : 0.19
% 7.58/2.68  CNF conversion       : 0.03
% 7.58/2.68  Main loop            : 1.53
% 7.58/2.68  Inferencing          : 0.56
% 7.58/2.68  Reduction            : 0.43
% 7.58/2.68  Demodulation         : 0.27
% 7.58/2.68  BG Simplification    : 0.06
% 7.58/2.68  Subsumption          : 0.37
% 7.58/2.68  Abstraction          : 0.06
% 7.58/2.68  MUC search           : 0.00
% 7.58/2.68  Cooper               : 0.00
% 7.58/2.68  Total                : 1.95
% 7.58/2.68  Index Insertion      : 0.00
% 7.58/2.68  Index Deletion       : 0.00
% 7.58/2.68  Index Matching       : 0.00
% 7.58/2.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
