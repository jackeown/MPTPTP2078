%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:45 EST 2020

% Result     : Theorem 4.61s
% Output     : CNFRefutation 4.71s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 378 expanded)
%              Number of leaves         :   39 ( 147 expanded)
%              Depth                    :   21
%              Number of atoms          :  447 (1686 expanded)
%              Number of equality atoms :    7 (  11 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_lattice3 > r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > k15_lattice3 > a_2_1_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(r3_lattices,type,(
    r3_lattices: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k16_lattice3,type,(
    k16_lattice3: ( $i * $i ) > $i )).

tff(k15_lattice3,type,(
    k15_lattice3: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v4_lattices,type,(
    v4_lattices: $i > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v6_lattices,type,(
    v6_lattices: $i > $o )).

tff(v9_lattices,type,(
    v9_lattices: $i > $o )).

tff(a_2_1_lattice3,type,(
    a_2_1_lattice3: ( $i * $i ) > $i )).

tff(r4_lattice3,type,(
    r4_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_lattice3,type,(
    v4_lattice3: $i > $o )).

tff(v5_lattices,type,(
    v5_lattices: $i > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff(v8_lattices,type,(
    v8_lattices: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(r3_lattice3,type,(
    r3_lattice3: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_179,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v4_lattice3(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( r2_hidden(B,C)
               => ( r3_lattices(A,B,k15_lattice3(A,C))
                  & r3_lattices(A,k16_lattice3(A,C),B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_lattice3)).

tff(f_138,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ! [B] : k16_lattice3(A,B) = k15_lattice3(A,a_2_1_lattice3(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d22_lattice3)).

tff(f_145,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => m1_subset_1(k15_lattice3(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).

tff(f_47,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( ( ~ v2_struct_0(A)
          & v10_lattices(A) )
       => ( ~ v2_struct_0(A)
          & v4_lattices(A)
          & v5_lattices(A)
          & v6_lattices(A)
          & v7_lattices(A)
          & v8_lattices(A)
          & v9_lattices(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & v8_lattices(A)
        & v9_lattices(A)
        & l3_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_lattices(A,B,C)
      <=> r1_lattices(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).

tff(f_130,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v4_lattice3(A)
          & l3_lattices(A) )
       => ! [B,C] :
            ( m1_subset_1(C,u1_struct_0(A))
           => ( C = k15_lattice3(A,B)
            <=> ( r4_lattice3(A,C,B)
                & ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r4_lattice3(A,D,B)
                     => r1_lattices(A,C,D) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d21_lattice3)).

tff(f_102,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( r4_lattice3(A,B,C)
            <=> ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( r2_hidden(D,C)
                   => r1_lattices(A,D,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattice3)).

tff(f_159,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & l3_lattices(B) )
     => ( r2_hidden(A,a_2_1_lattice3(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & r3_lattice3(B,D,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_lattice3)).

tff(f_84,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( r3_lattice3(A,B,C)
            <=> ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( r2_hidden(D,C)
                   => r1_lattices(A,B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattice3)).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_64,plain,(
    l3_lattices('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_506,plain,(
    ! [A_191,B_192] :
      ( k15_lattice3(A_191,a_2_1_lattice3(A_191,B_192)) = k16_lattice3(A_191,B_192)
      | ~ l3_lattices(A_191)
      | v2_struct_0(A_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_48,plain,(
    ! [A_64,B_65] :
      ( m1_subset_1(k15_lattice3(A_64,B_65),u1_struct_0(A_64))
      | ~ l3_lattices(A_64)
      | v2_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_512,plain,(
    ! [A_191,B_192] :
      ( m1_subset_1(k16_lattice3(A_191,B_192),u1_struct_0(A_191))
      | ~ l3_lattices(A_191)
      | v2_struct_0(A_191)
      | ~ l3_lattices(A_191)
      | v2_struct_0(A_191) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_506,c_48])).

tff(c_68,plain,(
    v10_lattices('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_4,plain,(
    ! [A_1] :
      ( v8_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [A_1] :
      ( v9_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_62,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_715,plain,(
    ! [A_251,B_252,C_253] :
      ( r3_lattices(A_251,B_252,C_253)
      | ~ r1_lattices(A_251,B_252,C_253)
      | ~ m1_subset_1(C_253,u1_struct_0(A_251))
      | ~ m1_subset_1(B_252,u1_struct_0(A_251))
      | ~ l3_lattices(A_251)
      | ~ v9_lattices(A_251)
      | ~ v8_lattices(A_251)
      | ~ v6_lattices(A_251)
      | v2_struct_0(A_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_727,plain,(
    ! [B_252] :
      ( r3_lattices('#skF_5',B_252,'#skF_6')
      | ~ r1_lattices('#skF_5',B_252,'#skF_6')
      | ~ m1_subset_1(B_252,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_62,c_715])).

tff(c_735,plain,(
    ! [B_252] :
      ( r3_lattices('#skF_5',B_252,'#skF_6')
      | ~ r1_lattices('#skF_5',B_252,'#skF_6')
      | ~ m1_subset_1(B_252,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_727])).

tff(c_736,plain,(
    ! [B_252] :
      ( r3_lattices('#skF_5',B_252,'#skF_6')
      | ~ r1_lattices('#skF_5',B_252,'#skF_6')
      | ~ m1_subset_1(B_252,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_735])).

tff(c_754,plain,(
    ~ v6_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_736])).

tff(c_757,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_754])).

tff(c_760,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_68,c_757])).

tff(c_762,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_760])).

tff(c_763,plain,(
    ! [B_252] :
      ( ~ v8_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | r3_lattices('#skF_5',B_252,'#skF_6')
      | ~ r1_lattices('#skF_5',B_252,'#skF_6')
      | ~ m1_subset_1(B_252,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_736])).

tff(c_765,plain,(
    ~ v9_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_763])).

tff(c_768,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_2,c_765])).

tff(c_771,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_68,c_768])).

tff(c_773,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_771])).

tff(c_774,plain,(
    ! [B_252] :
      ( ~ v8_lattices('#skF_5')
      | r3_lattices('#skF_5',B_252,'#skF_6')
      | ~ r1_lattices('#skF_5',B_252,'#skF_6')
      | ~ m1_subset_1(B_252,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_763])).

tff(c_783,plain,(
    ~ v8_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_774])).

tff(c_786,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_783])).

tff(c_789,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_68,c_786])).

tff(c_791,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_789])).

tff(c_803,plain,(
    ! [B_262] :
      ( r3_lattices('#skF_5',B_262,'#skF_6')
      | ~ r1_lattices('#skF_5',B_262,'#skF_6')
      | ~ m1_subset_1(B_262,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_774])).

tff(c_819,plain,(
    ! [B_192] :
      ( r3_lattices('#skF_5',k16_lattice3('#skF_5',B_192),'#skF_6')
      | ~ r1_lattices('#skF_5',k16_lattice3('#skF_5',B_192),'#skF_6')
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_512,c_803])).

tff(c_841,plain,(
    ! [B_192] :
      ( r3_lattices('#skF_5',k16_lattice3('#skF_5',B_192),'#skF_6')
      | ~ r1_lattices('#skF_5',k16_lattice3('#skF_5',B_192),'#skF_6')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_819])).

tff(c_849,plain,(
    ! [B_263] :
      ( r3_lattices('#skF_5',k16_lattice3('#skF_5',B_263),'#skF_6')
      | ~ r1_lattices('#skF_5',k16_lattice3('#skF_5',B_263),'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_841])).

tff(c_288,plain,(
    ! [A_144,B_145,C_146] :
      ( r3_lattices(A_144,B_145,C_146)
      | ~ r1_lattices(A_144,B_145,C_146)
      | ~ m1_subset_1(C_146,u1_struct_0(A_144))
      | ~ m1_subset_1(B_145,u1_struct_0(A_144))
      | ~ l3_lattices(A_144)
      | ~ v9_lattices(A_144)
      | ~ v8_lattices(A_144)
      | ~ v6_lattices(A_144)
      | v2_struct_0(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_300,plain,(
    ! [B_145] :
      ( r3_lattices('#skF_5',B_145,'#skF_6')
      | ~ r1_lattices('#skF_5',B_145,'#skF_6')
      | ~ m1_subset_1(B_145,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_62,c_288])).

tff(c_308,plain,(
    ! [B_145] :
      ( r3_lattices('#skF_5',B_145,'#skF_6')
      | ~ r1_lattices('#skF_5',B_145,'#skF_6')
      | ~ m1_subset_1(B_145,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_300])).

tff(c_309,plain,(
    ! [B_145] :
      ( r3_lattices('#skF_5',B_145,'#skF_6')
      | ~ r1_lattices('#skF_5',B_145,'#skF_6')
      | ~ m1_subset_1(B_145,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_308])).

tff(c_327,plain,(
    ~ v6_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_309])).

tff(c_330,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_327])).

tff(c_333,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_68,c_330])).

tff(c_335,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_333])).

tff(c_337,plain,(
    v6_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_309])).

tff(c_336,plain,(
    ! [B_145] :
      ( ~ v8_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | r3_lattices('#skF_5',B_145,'#skF_6')
      | ~ r1_lattices('#skF_5',B_145,'#skF_6')
      | ~ m1_subset_1(B_145,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_309])).

tff(c_338,plain,(
    ~ v9_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_336])).

tff(c_341,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_2,c_338])).

tff(c_344,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_68,c_341])).

tff(c_346,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_344])).

tff(c_347,plain,(
    ! [B_145] :
      ( ~ v8_lattices('#skF_5')
      | r3_lattices('#skF_5',B_145,'#skF_6')
      | ~ r1_lattices('#skF_5',B_145,'#skF_6')
      | ~ m1_subset_1(B_145,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_336])).

tff(c_350,plain,(
    ~ v8_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_347])).

tff(c_353,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_350])).

tff(c_356,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_68,c_353])).

tff(c_358,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_356])).

tff(c_360,plain,(
    v8_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_347])).

tff(c_348,plain,(
    v9_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_336])).

tff(c_66,plain,(
    v4_lattice3('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_120,plain,(
    ! [A_121,B_122] :
      ( r4_lattice3(A_121,k15_lattice3(A_121,B_122),B_122)
      | ~ m1_subset_1(k15_lattice3(A_121,B_122),u1_struct_0(A_121))
      | ~ v4_lattice3(A_121)
      | ~ v10_lattices(A_121)
      | ~ l3_lattices(A_121)
      | v2_struct_0(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_125,plain,(
    ! [A_64,B_65] :
      ( r4_lattice3(A_64,k15_lattice3(A_64,B_65),B_65)
      | ~ v4_lattice3(A_64)
      | ~ v10_lattices(A_64)
      | ~ l3_lattices(A_64)
      | v2_struct_0(A_64) ) ),
    inference(resolution,[status(thm)],[c_48,c_120])).

tff(c_60,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_126,plain,(
    ! [A_123,D_124,B_125,C_126] :
      ( r1_lattices(A_123,D_124,B_125)
      | ~ r2_hidden(D_124,C_126)
      | ~ m1_subset_1(D_124,u1_struct_0(A_123))
      | ~ r4_lattice3(A_123,B_125,C_126)
      | ~ m1_subset_1(B_125,u1_struct_0(A_123))
      | ~ l3_lattices(A_123)
      | v2_struct_0(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_143,plain,(
    ! [A_129,B_130] :
      ( r1_lattices(A_129,'#skF_6',B_130)
      | ~ m1_subset_1('#skF_6',u1_struct_0(A_129))
      | ~ r4_lattice3(A_129,B_130,'#skF_7')
      | ~ m1_subset_1(B_130,u1_struct_0(A_129))
      | ~ l3_lattices(A_129)
      | v2_struct_0(A_129) ) ),
    inference(resolution,[status(thm)],[c_60,c_126])).

tff(c_145,plain,(
    ! [B_130] :
      ( r1_lattices('#skF_5','#skF_6',B_130)
      | ~ r4_lattice3('#skF_5',B_130,'#skF_7')
      | ~ m1_subset_1(B_130,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_62,c_143])).

tff(c_148,plain,(
    ! [B_130] :
      ( r1_lattices('#skF_5','#skF_6',B_130)
      | ~ r4_lattice3('#skF_5',B_130,'#skF_7')
      | ~ m1_subset_1(B_130,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_145])).

tff(c_150,plain,(
    ! [B_131] :
      ( r1_lattices('#skF_5','#skF_6',B_131)
      | ~ r4_lattice3('#skF_5',B_131,'#skF_7')
      | ~ m1_subset_1(B_131,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_148])).

tff(c_170,plain,(
    ! [B_65] :
      ( r1_lattices('#skF_5','#skF_6',k15_lattice3('#skF_5',B_65))
      | ~ r4_lattice3('#skF_5',k15_lattice3('#skF_5',B_65),'#skF_7')
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_48,c_150])).

tff(c_192,plain,(
    ! [B_65] :
      ( r1_lattices('#skF_5','#skF_6',k15_lattice3('#skF_5',B_65))
      | ~ r4_lattice3('#skF_5',k15_lattice3('#skF_5',B_65),'#skF_7')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_170])).

tff(c_210,plain,(
    ! [B_137] :
      ( r1_lattices('#skF_5','#skF_6',k15_lattice3('#skF_5',B_137))
      | ~ r4_lattice3('#skF_5',k15_lattice3('#skF_5',B_137),'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_192])).

tff(c_214,plain,
    ( r1_lattices('#skF_5','#skF_6',k15_lattice3('#skF_5','#skF_7'))
    | ~ v4_lattice3('#skF_5')
    | ~ v10_lattices('#skF_5')
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_125,c_210])).

tff(c_221,plain,
    ( r1_lattices('#skF_5','#skF_6',k15_lattice3('#skF_5','#skF_7'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_68,c_66,c_214])).

tff(c_222,plain,(
    r1_lattices('#skF_5','#skF_6',k15_lattice3('#skF_5','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_221])).

tff(c_485,plain,(
    ! [A_183,B_184,B_185] :
      ( r3_lattices(A_183,B_184,k15_lattice3(A_183,B_185))
      | ~ r1_lattices(A_183,B_184,k15_lattice3(A_183,B_185))
      | ~ m1_subset_1(B_184,u1_struct_0(A_183))
      | ~ v9_lattices(A_183)
      | ~ v8_lattices(A_183)
      | ~ v6_lattices(A_183)
      | ~ l3_lattices(A_183)
      | v2_struct_0(A_183) ) ),
    inference(resolution,[status(thm)],[c_48,c_288])).

tff(c_58,plain,
    ( ~ r3_lattices('#skF_5',k16_lattice3('#skF_5','#skF_7'),'#skF_6')
    | ~ r3_lattices('#skF_5','#skF_6',k15_lattice3('#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_74,plain,(
    ~ r3_lattices('#skF_5','#skF_6',k15_lattice3('#skF_5','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_490,plain,
    ( ~ r1_lattices('#skF_5','#skF_6',k15_lattice3('#skF_5','#skF_7'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ v9_lattices('#skF_5')
    | ~ v8_lattices('#skF_5')
    | ~ v6_lattices('#skF_5')
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_485,c_74])).

tff(c_497,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_337,c_360,c_348,c_62,c_222,c_490])).

tff(c_499,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_497])).

tff(c_500,plain,(
    ~ r3_lattices('#skF_5',k16_lattice3('#skF_5','#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_859,plain,(
    ~ r1_lattices('#skF_5',k16_lattice3('#skF_5','#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_849,c_500])).

tff(c_32,plain,(
    ! [A_27,B_39,C_45] :
      ( r2_hidden('#skF_2'(A_27,B_39,C_45),C_45)
      | r4_lattice3(A_27,B_39,C_45)
      | ~ m1_subset_1(B_39,u1_struct_0(A_27))
      | ~ l3_lattices(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_537,plain,(
    ! [A_213,B_214,C_215] :
      ( r2_hidden('#skF_2'(A_213,B_214,C_215),C_215)
      | r4_lattice3(A_213,B_214,C_215)
      | ~ m1_subset_1(B_214,u1_struct_0(A_213))
      | ~ l3_lattices(A_213)
      | v2_struct_0(A_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_54,plain,(
    ! [A_66,B_67,C_68] :
      ( '#skF_4'(A_66,B_67,C_68) = A_66
      | ~ r2_hidden(A_66,a_2_1_lattice3(B_67,C_68))
      | ~ l3_lattices(B_67)
      | v2_struct_0(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_1432,plain,(
    ! [A_368,B_369,B_370,C_371] :
      ( '#skF_4'('#skF_2'(A_368,B_369,a_2_1_lattice3(B_370,C_371)),B_370,C_371) = '#skF_2'(A_368,B_369,a_2_1_lattice3(B_370,C_371))
      | ~ l3_lattices(B_370)
      | v2_struct_0(B_370)
      | r4_lattice3(A_368,B_369,a_2_1_lattice3(B_370,C_371))
      | ~ m1_subset_1(B_369,u1_struct_0(A_368))
      | ~ l3_lattices(A_368)
      | v2_struct_0(A_368) ) ),
    inference(resolution,[status(thm)],[c_537,c_54])).

tff(c_52,plain,(
    ! [B_67,A_66,C_68] :
      ( r3_lattice3(B_67,'#skF_4'(A_66,B_67,C_68),C_68)
      | ~ r2_hidden(A_66,a_2_1_lattice3(B_67,C_68))
      | ~ l3_lattices(B_67)
      | v2_struct_0(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_56,plain,(
    ! [A_66,B_67,C_68] :
      ( m1_subset_1('#skF_4'(A_66,B_67,C_68),u1_struct_0(B_67))
      | ~ r2_hidden(A_66,a_2_1_lattice3(B_67,C_68))
      | ~ l3_lattices(B_67)
      | v2_struct_0(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_623,plain,(
    ! [A_239,B_240,D_241,C_242] :
      ( r1_lattices(A_239,B_240,D_241)
      | ~ r2_hidden(D_241,C_242)
      | ~ m1_subset_1(D_241,u1_struct_0(A_239))
      | ~ r3_lattice3(A_239,B_240,C_242)
      | ~ m1_subset_1(B_240,u1_struct_0(A_239))
      | ~ l3_lattices(A_239)
      | v2_struct_0(A_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_662,plain,(
    ! [A_248,B_249] :
      ( r1_lattices(A_248,B_249,'#skF_6')
      | ~ m1_subset_1('#skF_6',u1_struct_0(A_248))
      | ~ r3_lattice3(A_248,B_249,'#skF_7')
      | ~ m1_subset_1(B_249,u1_struct_0(A_248))
      | ~ l3_lattices(A_248)
      | v2_struct_0(A_248) ) ),
    inference(resolution,[status(thm)],[c_60,c_623])).

tff(c_664,plain,(
    ! [B_249] :
      ( r1_lattices('#skF_5',B_249,'#skF_6')
      | ~ r3_lattice3('#skF_5',B_249,'#skF_7')
      | ~ m1_subset_1(B_249,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_62,c_662])).

tff(c_667,plain,(
    ! [B_249] :
      ( r1_lattices('#skF_5',B_249,'#skF_6')
      | ~ r3_lattice3('#skF_5',B_249,'#skF_7')
      | ~ m1_subset_1(B_249,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_664])).

tff(c_669,plain,(
    ! [B_250] :
      ( r1_lattices('#skF_5',B_250,'#skF_6')
      | ~ r3_lattice3('#skF_5',B_250,'#skF_7')
      | ~ m1_subset_1(B_250,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_667])).

tff(c_681,plain,(
    ! [A_66,C_68] :
      ( r1_lattices('#skF_5','#skF_4'(A_66,'#skF_5',C_68),'#skF_6')
      | ~ r3_lattice3('#skF_5','#skF_4'(A_66,'#skF_5',C_68),'#skF_7')
      | ~ r2_hidden(A_66,a_2_1_lattice3('#skF_5',C_68))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_56,c_669])).

tff(c_703,plain,(
    ! [A_66,C_68] :
      ( r1_lattices('#skF_5','#skF_4'(A_66,'#skF_5',C_68),'#skF_6')
      | ~ r3_lattice3('#skF_5','#skF_4'(A_66,'#skF_5',C_68),'#skF_7')
      | ~ r2_hidden(A_66,a_2_1_lattice3('#skF_5',C_68))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_681])).

tff(c_794,plain,(
    ! [A_260,C_261] :
      ( r1_lattices('#skF_5','#skF_4'(A_260,'#skF_5',C_261),'#skF_6')
      | ~ r3_lattice3('#skF_5','#skF_4'(A_260,'#skF_5',C_261),'#skF_7')
      | ~ r2_hidden(A_260,a_2_1_lattice3('#skF_5',C_261)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_703])).

tff(c_798,plain,(
    ! [A_66] :
      ( r1_lattices('#skF_5','#skF_4'(A_66,'#skF_5','#skF_7'),'#skF_6')
      | ~ r2_hidden(A_66,a_2_1_lattice3('#skF_5','#skF_7'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_52,c_794])).

tff(c_801,plain,(
    ! [A_66] :
      ( r1_lattices('#skF_5','#skF_4'(A_66,'#skF_5','#skF_7'),'#skF_6')
      | ~ r2_hidden(A_66,a_2_1_lattice3('#skF_5','#skF_7'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_798])).

tff(c_802,plain,(
    ! [A_66] :
      ( r1_lattices('#skF_5','#skF_4'(A_66,'#skF_5','#skF_7'),'#skF_6')
      | ~ r2_hidden(A_66,a_2_1_lattice3('#skF_5','#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_801])).

tff(c_1446,plain,(
    ! [A_368,B_369] :
      ( r1_lattices('#skF_5','#skF_2'(A_368,B_369,a_2_1_lattice3('#skF_5','#skF_7')),'#skF_6')
      | ~ r2_hidden('#skF_2'(A_368,B_369,a_2_1_lattice3('#skF_5','#skF_7')),a_2_1_lattice3('#skF_5','#skF_7'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5')
      | r4_lattice3(A_368,B_369,a_2_1_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1(B_369,u1_struct_0(A_368))
      | ~ l3_lattices(A_368)
      | v2_struct_0(A_368) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1432,c_802])).

tff(c_1469,plain,(
    ! [A_368,B_369] :
      ( r1_lattices('#skF_5','#skF_2'(A_368,B_369,a_2_1_lattice3('#skF_5','#skF_7')),'#skF_6')
      | ~ r2_hidden('#skF_2'(A_368,B_369,a_2_1_lattice3('#skF_5','#skF_7')),a_2_1_lattice3('#skF_5','#skF_7'))
      | v2_struct_0('#skF_5')
      | r4_lattice3(A_368,B_369,a_2_1_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1(B_369,u1_struct_0(A_368))
      | ~ l3_lattices(A_368)
      | v2_struct_0(A_368) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1446])).

tff(c_1614,plain,(
    ! [A_393,B_394] :
      ( r1_lattices('#skF_5','#skF_2'(A_393,B_394,a_2_1_lattice3('#skF_5','#skF_7')),'#skF_6')
      | ~ r2_hidden('#skF_2'(A_393,B_394,a_2_1_lattice3('#skF_5','#skF_7')),a_2_1_lattice3('#skF_5','#skF_7'))
      | r4_lattice3(A_393,B_394,a_2_1_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1(B_394,u1_struct_0(A_393))
      | ~ l3_lattices(A_393)
      | v2_struct_0(A_393) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1469])).

tff(c_1652,plain,(
    ! [A_400,B_401] :
      ( r1_lattices('#skF_5','#skF_2'(A_400,B_401,a_2_1_lattice3('#skF_5','#skF_7')),'#skF_6')
      | r4_lattice3(A_400,B_401,a_2_1_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1(B_401,u1_struct_0(A_400))
      | ~ l3_lattices(A_400)
      | v2_struct_0(A_400) ) ),
    inference(resolution,[status(thm)],[c_32,c_1614])).

tff(c_30,plain,(
    ! [A_27,B_39,C_45] :
      ( ~ r1_lattices(A_27,'#skF_2'(A_27,B_39,C_45),B_39)
      | r4_lattice3(A_27,B_39,C_45)
      | ~ m1_subset_1(B_39,u1_struct_0(A_27))
      | ~ l3_lattices(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1656,plain,
    ( r4_lattice3('#skF_5','#skF_6',a_2_1_lattice3('#skF_5','#skF_7'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1652,c_30])).

tff(c_1659,plain,
    ( r4_lattice3('#skF_5','#skF_6',a_2_1_lattice3('#skF_5','#skF_7'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_1656])).

tff(c_1660,plain,(
    r4_lattice3('#skF_5','#skF_6',a_2_1_lattice3('#skF_5','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1659])).

tff(c_46,plain,(
    ! [A_61,B_63] :
      ( k15_lattice3(A_61,a_2_1_lattice3(A_61,B_63)) = k16_lattice3(A_61,B_63)
      | ~ l3_lattices(A_61)
      | v2_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1007,plain,(
    ! [A_312,B_313,D_314] :
      ( r1_lattices(A_312,k15_lattice3(A_312,B_313),D_314)
      | ~ r4_lattice3(A_312,D_314,B_313)
      | ~ m1_subset_1(D_314,u1_struct_0(A_312))
      | ~ m1_subset_1(k15_lattice3(A_312,B_313),u1_struct_0(A_312))
      | ~ v4_lattice3(A_312)
      | ~ v10_lattices(A_312)
      | ~ l3_lattices(A_312)
      | v2_struct_0(A_312) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1013,plain,(
    ! [A_315,B_316,D_317] :
      ( r1_lattices(A_315,k15_lattice3(A_315,B_316),D_317)
      | ~ r4_lattice3(A_315,D_317,B_316)
      | ~ m1_subset_1(D_317,u1_struct_0(A_315))
      | ~ v4_lattice3(A_315)
      | ~ v10_lattices(A_315)
      | ~ l3_lattices(A_315)
      | v2_struct_0(A_315) ) ),
    inference(resolution,[status(thm)],[c_48,c_1007])).

tff(c_1027,plain,(
    ! [A_61,B_63,D_317] :
      ( r1_lattices(A_61,k16_lattice3(A_61,B_63),D_317)
      | ~ r4_lattice3(A_61,D_317,a_2_1_lattice3(A_61,B_63))
      | ~ m1_subset_1(D_317,u1_struct_0(A_61))
      | ~ v4_lattice3(A_61)
      | ~ v10_lattices(A_61)
      | ~ l3_lattices(A_61)
      | v2_struct_0(A_61)
      | ~ l3_lattices(A_61)
      | v2_struct_0(A_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_1013])).

tff(c_1666,plain,
    ( r1_lattices('#skF_5',k16_lattice3('#skF_5','#skF_7'),'#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ v4_lattice3('#skF_5')
    | ~ v10_lattices('#skF_5')
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1660,c_1027])).

tff(c_1676,plain,
    ( r1_lattices('#skF_5',k16_lattice3('#skF_5','#skF_7'),'#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_68,c_66,c_62,c_1666])).

tff(c_1678,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_859,c_1676])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:41:46 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.61/1.81  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.71/1.82  
% 4.71/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.71/1.83  %$ r4_lattice3 > r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > k15_lattice3 > a_2_1_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 4.71/1.83  
% 4.71/1.83  %Foreground sorts:
% 4.71/1.83  
% 4.71/1.83  
% 4.71/1.83  %Background operators:
% 4.71/1.83  
% 4.71/1.83  
% 4.71/1.83  %Foreground operators:
% 4.71/1.83  tff(l3_lattices, type, l3_lattices: $i > $o).
% 4.71/1.83  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.71/1.83  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.71/1.83  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 4.71/1.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.71/1.83  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.71/1.83  tff(k16_lattice3, type, k16_lattice3: ($i * $i) > $i).
% 4.71/1.83  tff(k15_lattice3, type, k15_lattice3: ($i * $i) > $i).
% 4.71/1.83  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.71/1.83  tff('#skF_7', type, '#skF_7': $i).
% 4.71/1.83  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 4.71/1.83  tff('#skF_5', type, '#skF_5': $i).
% 4.71/1.83  tff(v4_lattices, type, v4_lattices: $i > $o).
% 4.71/1.83  tff('#skF_6', type, '#skF_6': $i).
% 4.71/1.83  tff(v6_lattices, type, v6_lattices: $i > $o).
% 4.71/1.83  tff(v9_lattices, type, v9_lattices: $i > $o).
% 4.71/1.83  tff(a_2_1_lattice3, type, a_2_1_lattice3: ($i * $i) > $i).
% 4.71/1.83  tff(r4_lattice3, type, r4_lattice3: ($i * $i * $i) > $o).
% 4.71/1.83  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.71/1.83  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 4.71/1.83  tff(v5_lattices, type, v5_lattices: $i > $o).
% 4.71/1.83  tff(v10_lattices, type, v10_lattices: $i > $o).
% 4.71/1.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.71/1.83  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.71/1.83  tff(v8_lattices, type, v8_lattices: $i > $o).
% 4.71/1.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.71/1.83  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.71/1.83  tff(r3_lattice3, type, r3_lattice3: ($i * $i * $i) > $o).
% 4.71/1.83  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.71/1.83  tff(v7_lattices, type, v7_lattices: $i > $o).
% 4.71/1.83  
% 4.71/1.85  tff(f_179, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r2_hidden(B, C) => (r3_lattices(A, B, k15_lattice3(A, C)) & r3_lattices(A, k16_lattice3(A, C), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_lattice3)).
% 4.71/1.85  tff(f_138, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (k16_lattice3(A, B) = k15_lattice3(A, a_2_1_lattice3(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d22_lattice3)).
% 4.71/1.85  tff(f_145, axiom, (![A, B]: ((~v2_struct_0(A) & l3_lattices(A)) => m1_subset_1(k15_lattice3(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 4.71/1.85  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 4.71/1.85  tff(f_66, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_lattices(A, B, C) <=> r1_lattices(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 4.71/1.85  tff(f_130, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => ((C = k15_lattice3(A, B)) <=> (r4_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r4_lattice3(A, D, B) => r1_lattices(A, C, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d21_lattice3)).
% 4.71/1.85  tff(f_102, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r4_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, D, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_lattice3)).
% 4.71/1.85  tff(f_159, axiom, (![A, B, C]: ((~v2_struct_0(B) & l3_lattices(B)) => (r2_hidden(A, a_2_1_lattice3(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & r3_lattice3(B, D, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_1_lattice3)).
% 4.71/1.85  tff(f_84, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r3_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_lattice3)).
% 4.71/1.85  tff(c_70, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_179])).
% 4.71/1.85  tff(c_64, plain, (l3_lattices('#skF_5')), inference(cnfTransformation, [status(thm)], [f_179])).
% 4.71/1.85  tff(c_506, plain, (![A_191, B_192]: (k15_lattice3(A_191, a_2_1_lattice3(A_191, B_192))=k16_lattice3(A_191, B_192) | ~l3_lattices(A_191) | v2_struct_0(A_191))), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.71/1.85  tff(c_48, plain, (![A_64, B_65]: (m1_subset_1(k15_lattice3(A_64, B_65), u1_struct_0(A_64)) | ~l3_lattices(A_64) | v2_struct_0(A_64))), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.71/1.85  tff(c_512, plain, (![A_191, B_192]: (m1_subset_1(k16_lattice3(A_191, B_192), u1_struct_0(A_191)) | ~l3_lattices(A_191) | v2_struct_0(A_191) | ~l3_lattices(A_191) | v2_struct_0(A_191))), inference(superposition, [status(thm), theory('equality')], [c_506, c_48])).
% 4.71/1.85  tff(c_68, plain, (v10_lattices('#skF_5')), inference(cnfTransformation, [status(thm)], [f_179])).
% 4.71/1.85  tff(c_4, plain, (![A_1]: (v8_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.71/1.85  tff(c_2, plain, (![A_1]: (v9_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.71/1.85  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.71/1.85  tff(c_62, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_179])).
% 4.71/1.85  tff(c_715, plain, (![A_251, B_252, C_253]: (r3_lattices(A_251, B_252, C_253) | ~r1_lattices(A_251, B_252, C_253) | ~m1_subset_1(C_253, u1_struct_0(A_251)) | ~m1_subset_1(B_252, u1_struct_0(A_251)) | ~l3_lattices(A_251) | ~v9_lattices(A_251) | ~v8_lattices(A_251) | ~v6_lattices(A_251) | v2_struct_0(A_251))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.71/1.85  tff(c_727, plain, (![B_252]: (r3_lattices('#skF_5', B_252, '#skF_6') | ~r1_lattices('#skF_5', B_252, '#skF_6') | ~m1_subset_1(B_252, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_62, c_715])).
% 4.71/1.85  tff(c_735, plain, (![B_252]: (r3_lattices('#skF_5', B_252, '#skF_6') | ~r1_lattices('#skF_5', B_252, '#skF_6') | ~m1_subset_1(B_252, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_727])).
% 4.71/1.85  tff(c_736, plain, (![B_252]: (r3_lattices('#skF_5', B_252, '#skF_6') | ~r1_lattices('#skF_5', B_252, '#skF_6') | ~m1_subset_1(B_252, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_70, c_735])).
% 4.71/1.85  tff(c_754, plain, (~v6_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_736])).
% 4.71/1.85  tff(c_757, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_8, c_754])).
% 4.71/1.85  tff(c_760, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_68, c_757])).
% 4.71/1.85  tff(c_762, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_760])).
% 4.71/1.85  tff(c_763, plain, (![B_252]: (~v8_lattices('#skF_5') | ~v9_lattices('#skF_5') | r3_lattices('#skF_5', B_252, '#skF_6') | ~r1_lattices('#skF_5', B_252, '#skF_6') | ~m1_subset_1(B_252, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_736])).
% 4.71/1.85  tff(c_765, plain, (~v9_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_763])).
% 4.71/1.85  tff(c_768, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_2, c_765])).
% 4.71/1.85  tff(c_771, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_68, c_768])).
% 4.71/1.85  tff(c_773, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_771])).
% 4.71/1.85  tff(c_774, plain, (![B_252]: (~v8_lattices('#skF_5') | r3_lattices('#skF_5', B_252, '#skF_6') | ~r1_lattices('#skF_5', B_252, '#skF_6') | ~m1_subset_1(B_252, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_763])).
% 4.71/1.85  tff(c_783, plain, (~v8_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_774])).
% 4.71/1.85  tff(c_786, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_4, c_783])).
% 4.71/1.85  tff(c_789, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_68, c_786])).
% 4.71/1.85  tff(c_791, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_789])).
% 4.71/1.85  tff(c_803, plain, (![B_262]: (r3_lattices('#skF_5', B_262, '#skF_6') | ~r1_lattices('#skF_5', B_262, '#skF_6') | ~m1_subset_1(B_262, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_774])).
% 4.71/1.85  tff(c_819, plain, (![B_192]: (r3_lattices('#skF_5', k16_lattice3('#skF_5', B_192), '#skF_6') | ~r1_lattices('#skF_5', k16_lattice3('#skF_5', B_192), '#skF_6') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_512, c_803])).
% 4.71/1.85  tff(c_841, plain, (![B_192]: (r3_lattices('#skF_5', k16_lattice3('#skF_5', B_192), '#skF_6') | ~r1_lattices('#skF_5', k16_lattice3('#skF_5', B_192), '#skF_6') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_819])).
% 4.71/1.85  tff(c_849, plain, (![B_263]: (r3_lattices('#skF_5', k16_lattice3('#skF_5', B_263), '#skF_6') | ~r1_lattices('#skF_5', k16_lattice3('#skF_5', B_263), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_70, c_841])).
% 4.71/1.85  tff(c_288, plain, (![A_144, B_145, C_146]: (r3_lattices(A_144, B_145, C_146) | ~r1_lattices(A_144, B_145, C_146) | ~m1_subset_1(C_146, u1_struct_0(A_144)) | ~m1_subset_1(B_145, u1_struct_0(A_144)) | ~l3_lattices(A_144) | ~v9_lattices(A_144) | ~v8_lattices(A_144) | ~v6_lattices(A_144) | v2_struct_0(A_144))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.71/1.85  tff(c_300, plain, (![B_145]: (r3_lattices('#skF_5', B_145, '#skF_6') | ~r1_lattices('#skF_5', B_145, '#skF_6') | ~m1_subset_1(B_145, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_62, c_288])).
% 4.71/1.85  tff(c_308, plain, (![B_145]: (r3_lattices('#skF_5', B_145, '#skF_6') | ~r1_lattices('#skF_5', B_145, '#skF_6') | ~m1_subset_1(B_145, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_300])).
% 4.71/1.85  tff(c_309, plain, (![B_145]: (r3_lattices('#skF_5', B_145, '#skF_6') | ~r1_lattices('#skF_5', B_145, '#skF_6') | ~m1_subset_1(B_145, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_70, c_308])).
% 4.71/1.85  tff(c_327, plain, (~v6_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_309])).
% 4.71/1.85  tff(c_330, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_8, c_327])).
% 4.71/1.85  tff(c_333, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_68, c_330])).
% 4.71/1.85  tff(c_335, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_333])).
% 4.71/1.85  tff(c_337, plain, (v6_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_309])).
% 4.71/1.85  tff(c_336, plain, (![B_145]: (~v8_lattices('#skF_5') | ~v9_lattices('#skF_5') | r3_lattices('#skF_5', B_145, '#skF_6') | ~r1_lattices('#skF_5', B_145, '#skF_6') | ~m1_subset_1(B_145, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_309])).
% 4.71/1.85  tff(c_338, plain, (~v9_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_336])).
% 4.71/1.85  tff(c_341, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_2, c_338])).
% 4.71/1.85  tff(c_344, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_68, c_341])).
% 4.71/1.85  tff(c_346, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_344])).
% 4.71/1.85  tff(c_347, plain, (![B_145]: (~v8_lattices('#skF_5') | r3_lattices('#skF_5', B_145, '#skF_6') | ~r1_lattices('#skF_5', B_145, '#skF_6') | ~m1_subset_1(B_145, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_336])).
% 4.71/1.85  tff(c_350, plain, (~v8_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_347])).
% 4.71/1.85  tff(c_353, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_4, c_350])).
% 4.71/1.85  tff(c_356, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_68, c_353])).
% 4.71/1.85  tff(c_358, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_356])).
% 4.71/1.85  tff(c_360, plain, (v8_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_347])).
% 4.71/1.85  tff(c_348, plain, (v9_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_336])).
% 4.71/1.85  tff(c_66, plain, (v4_lattice3('#skF_5')), inference(cnfTransformation, [status(thm)], [f_179])).
% 4.71/1.85  tff(c_120, plain, (![A_121, B_122]: (r4_lattice3(A_121, k15_lattice3(A_121, B_122), B_122) | ~m1_subset_1(k15_lattice3(A_121, B_122), u1_struct_0(A_121)) | ~v4_lattice3(A_121) | ~v10_lattices(A_121) | ~l3_lattices(A_121) | v2_struct_0(A_121))), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.71/1.85  tff(c_125, plain, (![A_64, B_65]: (r4_lattice3(A_64, k15_lattice3(A_64, B_65), B_65) | ~v4_lattice3(A_64) | ~v10_lattices(A_64) | ~l3_lattices(A_64) | v2_struct_0(A_64))), inference(resolution, [status(thm)], [c_48, c_120])).
% 4.71/1.85  tff(c_60, plain, (r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_179])).
% 4.71/1.85  tff(c_126, plain, (![A_123, D_124, B_125, C_126]: (r1_lattices(A_123, D_124, B_125) | ~r2_hidden(D_124, C_126) | ~m1_subset_1(D_124, u1_struct_0(A_123)) | ~r4_lattice3(A_123, B_125, C_126) | ~m1_subset_1(B_125, u1_struct_0(A_123)) | ~l3_lattices(A_123) | v2_struct_0(A_123))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.71/1.85  tff(c_143, plain, (![A_129, B_130]: (r1_lattices(A_129, '#skF_6', B_130) | ~m1_subset_1('#skF_6', u1_struct_0(A_129)) | ~r4_lattice3(A_129, B_130, '#skF_7') | ~m1_subset_1(B_130, u1_struct_0(A_129)) | ~l3_lattices(A_129) | v2_struct_0(A_129))), inference(resolution, [status(thm)], [c_60, c_126])).
% 4.71/1.85  tff(c_145, plain, (![B_130]: (r1_lattices('#skF_5', '#skF_6', B_130) | ~r4_lattice3('#skF_5', B_130, '#skF_7') | ~m1_subset_1(B_130, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_62, c_143])).
% 4.71/1.85  tff(c_148, plain, (![B_130]: (r1_lattices('#skF_5', '#skF_6', B_130) | ~r4_lattice3('#skF_5', B_130, '#skF_7') | ~m1_subset_1(B_130, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_145])).
% 4.71/1.85  tff(c_150, plain, (![B_131]: (r1_lattices('#skF_5', '#skF_6', B_131) | ~r4_lattice3('#skF_5', B_131, '#skF_7') | ~m1_subset_1(B_131, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_70, c_148])).
% 4.71/1.85  tff(c_170, plain, (![B_65]: (r1_lattices('#skF_5', '#skF_6', k15_lattice3('#skF_5', B_65)) | ~r4_lattice3('#skF_5', k15_lattice3('#skF_5', B_65), '#skF_7') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_48, c_150])).
% 4.71/1.85  tff(c_192, plain, (![B_65]: (r1_lattices('#skF_5', '#skF_6', k15_lattice3('#skF_5', B_65)) | ~r4_lattice3('#skF_5', k15_lattice3('#skF_5', B_65), '#skF_7') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_170])).
% 4.71/1.85  tff(c_210, plain, (![B_137]: (r1_lattices('#skF_5', '#skF_6', k15_lattice3('#skF_5', B_137)) | ~r4_lattice3('#skF_5', k15_lattice3('#skF_5', B_137), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_70, c_192])).
% 4.71/1.85  tff(c_214, plain, (r1_lattices('#skF_5', '#skF_6', k15_lattice3('#skF_5', '#skF_7')) | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_125, c_210])).
% 4.71/1.85  tff(c_221, plain, (r1_lattices('#skF_5', '#skF_6', k15_lattice3('#skF_5', '#skF_7')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_68, c_66, c_214])).
% 4.71/1.85  tff(c_222, plain, (r1_lattices('#skF_5', '#skF_6', k15_lattice3('#skF_5', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_70, c_221])).
% 4.71/1.85  tff(c_485, plain, (![A_183, B_184, B_185]: (r3_lattices(A_183, B_184, k15_lattice3(A_183, B_185)) | ~r1_lattices(A_183, B_184, k15_lattice3(A_183, B_185)) | ~m1_subset_1(B_184, u1_struct_0(A_183)) | ~v9_lattices(A_183) | ~v8_lattices(A_183) | ~v6_lattices(A_183) | ~l3_lattices(A_183) | v2_struct_0(A_183))), inference(resolution, [status(thm)], [c_48, c_288])).
% 4.71/1.86  tff(c_58, plain, (~r3_lattices('#skF_5', k16_lattice3('#skF_5', '#skF_7'), '#skF_6') | ~r3_lattices('#skF_5', '#skF_6', k15_lattice3('#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_179])).
% 4.71/1.86  tff(c_74, plain, (~r3_lattices('#skF_5', '#skF_6', k15_lattice3('#skF_5', '#skF_7'))), inference(splitLeft, [status(thm)], [c_58])).
% 4.71/1.86  tff(c_490, plain, (~r1_lattices('#skF_5', '#skF_6', k15_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_485, c_74])).
% 4.71/1.86  tff(c_497, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_337, c_360, c_348, c_62, c_222, c_490])).
% 4.71/1.86  tff(c_499, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_497])).
% 4.71/1.86  tff(c_500, plain, (~r3_lattices('#skF_5', k16_lattice3('#skF_5', '#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_58])).
% 4.71/1.86  tff(c_859, plain, (~r1_lattices('#skF_5', k16_lattice3('#skF_5', '#skF_7'), '#skF_6')), inference(resolution, [status(thm)], [c_849, c_500])).
% 4.71/1.86  tff(c_32, plain, (![A_27, B_39, C_45]: (r2_hidden('#skF_2'(A_27, B_39, C_45), C_45) | r4_lattice3(A_27, B_39, C_45) | ~m1_subset_1(B_39, u1_struct_0(A_27)) | ~l3_lattices(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.71/1.86  tff(c_537, plain, (![A_213, B_214, C_215]: (r2_hidden('#skF_2'(A_213, B_214, C_215), C_215) | r4_lattice3(A_213, B_214, C_215) | ~m1_subset_1(B_214, u1_struct_0(A_213)) | ~l3_lattices(A_213) | v2_struct_0(A_213))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.71/1.86  tff(c_54, plain, (![A_66, B_67, C_68]: ('#skF_4'(A_66, B_67, C_68)=A_66 | ~r2_hidden(A_66, a_2_1_lattice3(B_67, C_68)) | ~l3_lattices(B_67) | v2_struct_0(B_67))), inference(cnfTransformation, [status(thm)], [f_159])).
% 4.71/1.86  tff(c_1432, plain, (![A_368, B_369, B_370, C_371]: ('#skF_4'('#skF_2'(A_368, B_369, a_2_1_lattice3(B_370, C_371)), B_370, C_371)='#skF_2'(A_368, B_369, a_2_1_lattice3(B_370, C_371)) | ~l3_lattices(B_370) | v2_struct_0(B_370) | r4_lattice3(A_368, B_369, a_2_1_lattice3(B_370, C_371)) | ~m1_subset_1(B_369, u1_struct_0(A_368)) | ~l3_lattices(A_368) | v2_struct_0(A_368))), inference(resolution, [status(thm)], [c_537, c_54])).
% 4.71/1.86  tff(c_52, plain, (![B_67, A_66, C_68]: (r3_lattice3(B_67, '#skF_4'(A_66, B_67, C_68), C_68) | ~r2_hidden(A_66, a_2_1_lattice3(B_67, C_68)) | ~l3_lattices(B_67) | v2_struct_0(B_67))), inference(cnfTransformation, [status(thm)], [f_159])).
% 4.71/1.86  tff(c_56, plain, (![A_66, B_67, C_68]: (m1_subset_1('#skF_4'(A_66, B_67, C_68), u1_struct_0(B_67)) | ~r2_hidden(A_66, a_2_1_lattice3(B_67, C_68)) | ~l3_lattices(B_67) | v2_struct_0(B_67))), inference(cnfTransformation, [status(thm)], [f_159])).
% 4.71/1.86  tff(c_623, plain, (![A_239, B_240, D_241, C_242]: (r1_lattices(A_239, B_240, D_241) | ~r2_hidden(D_241, C_242) | ~m1_subset_1(D_241, u1_struct_0(A_239)) | ~r3_lattice3(A_239, B_240, C_242) | ~m1_subset_1(B_240, u1_struct_0(A_239)) | ~l3_lattices(A_239) | v2_struct_0(A_239))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.71/1.86  tff(c_662, plain, (![A_248, B_249]: (r1_lattices(A_248, B_249, '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0(A_248)) | ~r3_lattice3(A_248, B_249, '#skF_7') | ~m1_subset_1(B_249, u1_struct_0(A_248)) | ~l3_lattices(A_248) | v2_struct_0(A_248))), inference(resolution, [status(thm)], [c_60, c_623])).
% 4.71/1.86  tff(c_664, plain, (![B_249]: (r1_lattices('#skF_5', B_249, '#skF_6') | ~r3_lattice3('#skF_5', B_249, '#skF_7') | ~m1_subset_1(B_249, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_62, c_662])).
% 4.71/1.86  tff(c_667, plain, (![B_249]: (r1_lattices('#skF_5', B_249, '#skF_6') | ~r3_lattice3('#skF_5', B_249, '#skF_7') | ~m1_subset_1(B_249, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_664])).
% 4.71/1.86  tff(c_669, plain, (![B_250]: (r1_lattices('#skF_5', B_250, '#skF_6') | ~r3_lattice3('#skF_5', B_250, '#skF_7') | ~m1_subset_1(B_250, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_70, c_667])).
% 4.71/1.86  tff(c_681, plain, (![A_66, C_68]: (r1_lattices('#skF_5', '#skF_4'(A_66, '#skF_5', C_68), '#skF_6') | ~r3_lattice3('#skF_5', '#skF_4'(A_66, '#skF_5', C_68), '#skF_7') | ~r2_hidden(A_66, a_2_1_lattice3('#skF_5', C_68)) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_56, c_669])).
% 4.71/1.86  tff(c_703, plain, (![A_66, C_68]: (r1_lattices('#skF_5', '#skF_4'(A_66, '#skF_5', C_68), '#skF_6') | ~r3_lattice3('#skF_5', '#skF_4'(A_66, '#skF_5', C_68), '#skF_7') | ~r2_hidden(A_66, a_2_1_lattice3('#skF_5', C_68)) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_681])).
% 4.71/1.86  tff(c_794, plain, (![A_260, C_261]: (r1_lattices('#skF_5', '#skF_4'(A_260, '#skF_5', C_261), '#skF_6') | ~r3_lattice3('#skF_5', '#skF_4'(A_260, '#skF_5', C_261), '#skF_7') | ~r2_hidden(A_260, a_2_1_lattice3('#skF_5', C_261)))), inference(negUnitSimplification, [status(thm)], [c_70, c_703])).
% 4.71/1.86  tff(c_798, plain, (![A_66]: (r1_lattices('#skF_5', '#skF_4'(A_66, '#skF_5', '#skF_7'), '#skF_6') | ~r2_hidden(A_66, a_2_1_lattice3('#skF_5', '#skF_7')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_52, c_794])).
% 4.71/1.86  tff(c_801, plain, (![A_66]: (r1_lattices('#skF_5', '#skF_4'(A_66, '#skF_5', '#skF_7'), '#skF_6') | ~r2_hidden(A_66, a_2_1_lattice3('#skF_5', '#skF_7')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_798])).
% 4.71/1.86  tff(c_802, plain, (![A_66]: (r1_lattices('#skF_5', '#skF_4'(A_66, '#skF_5', '#skF_7'), '#skF_6') | ~r2_hidden(A_66, a_2_1_lattice3('#skF_5', '#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_70, c_801])).
% 4.71/1.86  tff(c_1446, plain, (![A_368, B_369]: (r1_lattices('#skF_5', '#skF_2'(A_368, B_369, a_2_1_lattice3('#skF_5', '#skF_7')), '#skF_6') | ~r2_hidden('#skF_2'(A_368, B_369, a_2_1_lattice3('#skF_5', '#skF_7')), a_2_1_lattice3('#skF_5', '#skF_7')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5') | r4_lattice3(A_368, B_369, a_2_1_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(B_369, u1_struct_0(A_368)) | ~l3_lattices(A_368) | v2_struct_0(A_368))), inference(superposition, [status(thm), theory('equality')], [c_1432, c_802])).
% 4.71/1.86  tff(c_1469, plain, (![A_368, B_369]: (r1_lattices('#skF_5', '#skF_2'(A_368, B_369, a_2_1_lattice3('#skF_5', '#skF_7')), '#skF_6') | ~r2_hidden('#skF_2'(A_368, B_369, a_2_1_lattice3('#skF_5', '#skF_7')), a_2_1_lattice3('#skF_5', '#skF_7')) | v2_struct_0('#skF_5') | r4_lattice3(A_368, B_369, a_2_1_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(B_369, u1_struct_0(A_368)) | ~l3_lattices(A_368) | v2_struct_0(A_368))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1446])).
% 4.71/1.86  tff(c_1614, plain, (![A_393, B_394]: (r1_lattices('#skF_5', '#skF_2'(A_393, B_394, a_2_1_lattice3('#skF_5', '#skF_7')), '#skF_6') | ~r2_hidden('#skF_2'(A_393, B_394, a_2_1_lattice3('#skF_5', '#skF_7')), a_2_1_lattice3('#skF_5', '#skF_7')) | r4_lattice3(A_393, B_394, a_2_1_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(B_394, u1_struct_0(A_393)) | ~l3_lattices(A_393) | v2_struct_0(A_393))), inference(negUnitSimplification, [status(thm)], [c_70, c_1469])).
% 4.71/1.86  tff(c_1652, plain, (![A_400, B_401]: (r1_lattices('#skF_5', '#skF_2'(A_400, B_401, a_2_1_lattice3('#skF_5', '#skF_7')), '#skF_6') | r4_lattice3(A_400, B_401, a_2_1_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(B_401, u1_struct_0(A_400)) | ~l3_lattices(A_400) | v2_struct_0(A_400))), inference(resolution, [status(thm)], [c_32, c_1614])).
% 4.71/1.86  tff(c_30, plain, (![A_27, B_39, C_45]: (~r1_lattices(A_27, '#skF_2'(A_27, B_39, C_45), B_39) | r4_lattice3(A_27, B_39, C_45) | ~m1_subset_1(B_39, u1_struct_0(A_27)) | ~l3_lattices(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.71/1.86  tff(c_1656, plain, (r4_lattice3('#skF_5', '#skF_6', a_2_1_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_1652, c_30])).
% 4.71/1.86  tff(c_1659, plain, (r4_lattice3('#skF_5', '#skF_6', a_2_1_lattice3('#skF_5', '#skF_7')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_1656])).
% 4.71/1.86  tff(c_1660, plain, (r4_lattice3('#skF_5', '#skF_6', a_2_1_lattice3('#skF_5', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_70, c_1659])).
% 4.71/1.86  tff(c_46, plain, (![A_61, B_63]: (k15_lattice3(A_61, a_2_1_lattice3(A_61, B_63))=k16_lattice3(A_61, B_63) | ~l3_lattices(A_61) | v2_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.71/1.86  tff(c_1007, plain, (![A_312, B_313, D_314]: (r1_lattices(A_312, k15_lattice3(A_312, B_313), D_314) | ~r4_lattice3(A_312, D_314, B_313) | ~m1_subset_1(D_314, u1_struct_0(A_312)) | ~m1_subset_1(k15_lattice3(A_312, B_313), u1_struct_0(A_312)) | ~v4_lattice3(A_312) | ~v10_lattices(A_312) | ~l3_lattices(A_312) | v2_struct_0(A_312))), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.71/1.86  tff(c_1013, plain, (![A_315, B_316, D_317]: (r1_lattices(A_315, k15_lattice3(A_315, B_316), D_317) | ~r4_lattice3(A_315, D_317, B_316) | ~m1_subset_1(D_317, u1_struct_0(A_315)) | ~v4_lattice3(A_315) | ~v10_lattices(A_315) | ~l3_lattices(A_315) | v2_struct_0(A_315))), inference(resolution, [status(thm)], [c_48, c_1007])).
% 4.71/1.86  tff(c_1027, plain, (![A_61, B_63, D_317]: (r1_lattices(A_61, k16_lattice3(A_61, B_63), D_317) | ~r4_lattice3(A_61, D_317, a_2_1_lattice3(A_61, B_63)) | ~m1_subset_1(D_317, u1_struct_0(A_61)) | ~v4_lattice3(A_61) | ~v10_lattices(A_61) | ~l3_lattices(A_61) | v2_struct_0(A_61) | ~l3_lattices(A_61) | v2_struct_0(A_61))), inference(superposition, [status(thm), theory('equality')], [c_46, c_1013])).
% 4.71/1.86  tff(c_1666, plain, (r1_lattices('#skF_5', k16_lattice3('#skF_5', '#skF_7'), '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_1660, c_1027])).
% 4.71/1.86  tff(c_1676, plain, (r1_lattices('#skF_5', k16_lattice3('#skF_5', '#skF_7'), '#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_68, c_66, c_62, c_1666])).
% 4.71/1.86  tff(c_1678, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_859, c_1676])).
% 4.71/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.71/1.86  
% 4.71/1.86  Inference rules
% 4.71/1.86  ----------------------
% 4.71/1.86  #Ref     : 0
% 4.71/1.86  #Sup     : 267
% 4.71/1.86  #Fact    : 0
% 4.71/1.86  #Define  : 0
% 4.71/1.86  #Split   : 13
% 4.71/1.86  #Chain   : 0
% 4.71/1.86  #Close   : 0
% 4.71/1.86  
% 4.71/1.86  Ordering : KBO
% 4.71/1.86  
% 4.71/1.86  Simplification rules
% 4.71/1.86  ----------------------
% 4.71/1.86  #Subsume      : 40
% 4.71/1.86  #Demod        : 257
% 4.71/1.86  #Tautology    : 33
% 4.71/1.86  #SimpNegUnit  : 133
% 4.71/1.86  #BackRed      : 0
% 4.71/1.86  
% 4.71/1.86  #Partial instantiations: 0
% 4.71/1.86  #Strategies tried      : 1
% 4.71/1.86  
% 4.71/1.86  Timing (in seconds)
% 4.71/1.86  ----------------------
% 4.71/1.86  Preprocessing        : 0.34
% 4.71/1.86  Parsing              : 0.18
% 4.71/1.86  CNF conversion       : 0.03
% 4.71/1.86  Main loop            : 0.73
% 4.71/1.86  Inferencing          : 0.30
% 4.71/1.86  Reduction            : 0.19
% 4.71/1.86  Demodulation         : 0.12
% 4.71/1.86  BG Simplification    : 0.03
% 4.71/1.86  Subsumption          : 0.14
% 4.71/1.86  Abstraction          : 0.03
% 4.71/1.86  MUC search           : 0.00
% 4.71/1.86  Cooper               : 0.00
% 4.71/1.86  Total                : 1.13
% 4.71/1.86  Index Insertion      : 0.00
% 4.71/1.86  Index Deletion       : 0.00
% 4.71/1.86  Index Matching       : 0.00
% 4.71/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
