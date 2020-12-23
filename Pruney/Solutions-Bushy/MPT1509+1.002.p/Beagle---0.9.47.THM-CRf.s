%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1509+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:59 EST 2020

% Result     : Theorem 43.52s
% Output     : CNFRefutation 43.65s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 498 expanded)
%              Number of leaves         :   47 ( 190 expanded)
%              Depth                    :   16
%              Number of atoms          :  436 (1928 expanded)
%              Number of equality atoms :   48 ( 300 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_lattice3 > r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v1_xboole_0 > v10_lattices > l3_lattices > l2_lattices > l1_struct_0 > l1_lattices > k6_domain_1 > k16_lattice3 > k15_lattice3 > #nlpp > u1_struct_0 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(l2_lattices,type,(
    l2_lattices: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(r3_lattices,type,(
    r3_lattices: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k16_lattice3,type,(
    k16_lattice3: ( $i * $i ) > $i )).

tff(k15_lattice3,type,(
    k15_lattice3: ( $i * $i ) > $i )).

tff(l1_lattices,type,(
    l1_lattices: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v8_lattices,type,(
    v8_lattices: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(r3_lattice3,type,(
    r3_lattice3: ( $i * $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_223,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v4_lattice3(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( k15_lattice3(A,k6_domain_1(u1_struct_0(A),B)) = B
              & k16_lattice3(A,k6_domain_1(u1_struct_0(A),B)) = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_lattice3)).

tff(f_106,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_100,axiom,(
    ! [A] :
      ( l1_lattices(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_lattices)).

tff(f_121,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_114,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_89,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_46,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).

tff(f_157,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & v8_lattices(A)
        & v9_lattices(A)
        & l3_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => r3_lattices(A,B,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_lattices)).

tff(f_140,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).

tff(f_82,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattice3)).

tff(f_182,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v4_lattice3(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( ( r2_hidden(B,C)
                & r4_lattice3(A,B,C) )
             => k15_lattice3(A,C) = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_lattice3)).

tff(f_64,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattice3)).

tff(f_201,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v4_lattice3(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( ( r2_hidden(B,C)
                & r3_lattice3(A,B,C) )
             => k16_lattice3(A,C) = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_lattice3)).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_74,plain,(
    l3_lattices('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_81,plain,(
    ! [A_83] :
      ( l1_lattices(A_83)
      | ~ l3_lattices(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_85,plain,(
    l1_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_81])).

tff(c_46,plain,(
    ! [A_53] :
      ( l1_struct_0(A_53)
      | ~ l1_lattices(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_72,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_150287,plain,(
    ! [A_88456,B_88457] :
      ( k6_domain_1(A_88456,B_88457) = k1_tarski(B_88457)
      | ~ m1_subset_1(B_88457,A_88456)
      | v1_xboole_0(A_88456) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_150291,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_72,c_150287])).

tff(c_150303,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_150291])).

tff(c_52,plain,(
    ! [A_55] :
      ( ~ v1_xboole_0(u1_struct_0(A_55))
      | ~ l1_struct_0(A_55)
      | v2_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_150306,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_150303,c_52])).

tff(c_150309,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_150306])).

tff(c_150312,plain,(
    ~ l1_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_150309])).

tff(c_150316,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_150312])).

tff(c_150317,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_150291])).

tff(c_126,plain,(
    ! [A_103,B_104] :
      ( k6_domain_1(A_103,B_104) = k1_tarski(B_104)
      | ~ m1_subset_1(B_104,A_103)
      | v1_xboole_0(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_130,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_72,c_126])).

tff(c_131,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_130])).

tff(c_134,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_131,c_52])).

tff(c_137,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_134])).

tff(c_140,plain,(
    ~ l1_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_137])).

tff(c_144,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_140])).

tff(c_145,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_130])).

tff(c_70,plain,
    ( k16_lattice3('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_6')) != '#skF_6'
    | k15_lattice3('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_6')) != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_121,plain,(
    k15_lattice3('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_6')) != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_147,plain,(
    k15_lattice3('#skF_5',k1_tarski('#skF_6')) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_121])).

tff(c_78,plain,(
    v10_lattices('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_76,plain,(
    v4_lattice3('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_34,plain,(
    ! [C_50] : r2_hidden(C_50,k1_tarski(C_50)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_16119,plain,(
    ! [A_8578,B_8579,C_8580] :
      ( r3_lattices(A_8578,B_8579,B_8579)
      | ~ m1_subset_1(C_8580,u1_struct_0(A_8578))
      | ~ m1_subset_1(B_8579,u1_struct_0(A_8578))
      | ~ l3_lattices(A_8578)
      | ~ v9_lattices(A_8578)
      | ~ v8_lattices(A_8578)
      | ~ v6_lattices(A_8578)
      | v2_struct_0(A_8578) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_16143,plain,(
    ! [B_8579] :
      ( r3_lattices('#skF_5',B_8579,B_8579)
      | ~ m1_subset_1(B_8579,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_72,c_16119])).

tff(c_16149,plain,(
    ! [B_8579] :
      ( r3_lattices('#skF_5',B_8579,B_8579)
      | ~ m1_subset_1(B_8579,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_16143])).

tff(c_16150,plain,(
    ! [B_8579] :
      ( r3_lattices('#skF_5',B_8579,B_8579)
      | ~ m1_subset_1(B_8579,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_16149])).

tff(c_16151,plain,(
    ~ v6_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_16150])).

tff(c_16158,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_16151])).

tff(c_16161,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_78,c_16158])).

tff(c_16163,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_16161])).

tff(c_16165,plain,(
    v6_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_16150])).

tff(c_4,plain,(
    ! [A_1] :
      ( v8_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [A_1] :
      ( v9_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_16164,plain,(
    ! [B_8579] :
      ( ~ v8_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | r3_lattices('#skF_5',B_8579,B_8579)
      | ~ m1_subset_1(B_8579,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_16150])).

tff(c_16214,plain,(
    ~ v9_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_16164])).

tff(c_16221,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_2,c_16214])).

tff(c_16224,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_78,c_16221])).

tff(c_16226,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_16224])).

tff(c_16227,plain,(
    ! [B_8579] :
      ( ~ v8_lattices('#skF_5')
      | r3_lattices('#skF_5',B_8579,B_8579)
      | ~ m1_subset_1(B_8579,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_16164])).

tff(c_16277,plain,(
    ~ v8_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_16227])).

tff(c_16284,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_16277])).

tff(c_16287,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_78,c_16284])).

tff(c_16289,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_16287])).

tff(c_16291,plain,(
    v8_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_16227])).

tff(c_16228,plain,(
    v9_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_16164])).

tff(c_16397,plain,(
    ! [B_9448] :
      ( r3_lattices('#skF_5',B_9448,B_9448)
      | ~ m1_subset_1(B_9448,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_16227])).

tff(c_16482,plain,(
    r3_lattices('#skF_5','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_72,c_16397])).

tff(c_32191,plain,(
    ! [A_21295,B_21296,C_21297] :
      ( r1_lattices(A_21295,B_21296,C_21297)
      | ~ r3_lattices(A_21295,B_21296,C_21297)
      | ~ m1_subset_1(C_21297,u1_struct_0(A_21295))
      | ~ m1_subset_1(B_21296,u1_struct_0(A_21295))
      | ~ l3_lattices(A_21295)
      | ~ v9_lattices(A_21295)
      | ~ v8_lattices(A_21295)
      | ~ v6_lattices(A_21295)
      | v2_struct_0(A_21295) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_32207,plain,
    ( r1_lattices('#skF_5','#skF_6','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | ~ v9_lattices('#skF_5')
    | ~ v8_lattices('#skF_5')
    | ~ v6_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_16482,c_32191])).

tff(c_32235,plain,
    ( r1_lattices('#skF_5','#skF_6','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16165,c_16291,c_16228,c_74,c_72,c_32207])).

tff(c_32236,plain,(
    r1_lattices('#skF_5','#skF_6','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_32235])).

tff(c_489,plain,(
    ! [A_925,B_926,C_927] :
      ( r2_hidden('#skF_2'(A_925,B_926,C_927),C_927)
      | r4_lattice3(A_925,B_926,C_927)
      | ~ m1_subset_1(B_926,u1_struct_0(A_925))
      | ~ l3_lattices(A_925)
      | v2_struct_0(A_925) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_32,plain,(
    ! [C_50,A_46] :
      ( C_50 = A_46
      | ~ r2_hidden(C_50,k1_tarski(A_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_501,plain,(
    ! [A_925,B_926,A_46] :
      ( '#skF_2'(A_925,B_926,k1_tarski(A_46)) = A_46
      | r4_lattice3(A_925,B_926,k1_tarski(A_46))
      | ~ m1_subset_1(B_926,u1_struct_0(A_925))
      | ~ l3_lattices(A_925)
      | v2_struct_0(A_925) ) ),
    inference(resolution,[status(thm)],[c_489,c_32])).

tff(c_18021,plain,(
    ! [A_10102,C_10103,B_10104] :
      ( k15_lattice3(A_10102,C_10103) = B_10104
      | ~ r4_lattice3(A_10102,B_10104,C_10103)
      | ~ r2_hidden(B_10104,C_10103)
      | ~ m1_subset_1(B_10104,u1_struct_0(A_10102))
      | ~ l3_lattices(A_10102)
      | ~ v4_lattice3(A_10102)
      | ~ v10_lattices(A_10102)
      | v2_struct_0(A_10102) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_142005,plain,(
    ! [A_80740,A_80741,B_80742] :
      ( k15_lattice3(A_80740,k1_tarski(A_80741)) = B_80742
      | ~ r2_hidden(B_80742,k1_tarski(A_80741))
      | ~ v4_lattice3(A_80740)
      | ~ v10_lattices(A_80740)
      | '#skF_2'(A_80740,B_80742,k1_tarski(A_80741)) = A_80741
      | ~ m1_subset_1(B_80742,u1_struct_0(A_80740))
      | ~ l3_lattices(A_80740)
      | v2_struct_0(A_80740) ) ),
    inference(resolution,[status(thm)],[c_501,c_18021])).

tff(c_149338,plain,(
    ! [A_87653,C_87654] :
      ( k15_lattice3(A_87653,k1_tarski(C_87654)) = C_87654
      | ~ v4_lattice3(A_87653)
      | ~ v10_lattices(A_87653)
      | '#skF_2'(A_87653,C_87654,k1_tarski(C_87654)) = C_87654
      | ~ m1_subset_1(C_87654,u1_struct_0(A_87653))
      | ~ l3_lattices(A_87653)
      | v2_struct_0(A_87653) ) ),
    inference(resolution,[status(thm)],[c_34,c_142005])).

tff(c_149518,plain,
    ( k15_lattice3('#skF_5',k1_tarski('#skF_6')) = '#skF_6'
    | ~ v4_lattice3('#skF_5')
    | ~ v10_lattices('#skF_5')
    | '#skF_2'('#skF_5','#skF_6',k1_tarski('#skF_6')) = '#skF_6'
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_149338])).

tff(c_149526,plain,
    ( k15_lattice3('#skF_5',k1_tarski('#skF_6')) = '#skF_6'
    | '#skF_2'('#skF_5','#skF_6',k1_tarski('#skF_6')) = '#skF_6'
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_78,c_76,c_149518])).

tff(c_149527,plain,(
    '#skF_2'('#skF_5','#skF_6',k1_tarski('#skF_6')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_147,c_149526])).

tff(c_26,plain,(
    ! [A_24,B_36,C_42] :
      ( ~ r1_lattices(A_24,'#skF_2'(A_24,B_36,C_42),B_36)
      | r4_lattice3(A_24,B_36,C_42)
      | ~ m1_subset_1(B_36,u1_struct_0(A_24))
      | ~ l3_lattices(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_149792,plain,
    ( ~ r1_lattices('#skF_5','#skF_6','#skF_6')
    | r4_lattice3('#skF_5','#skF_6',k1_tarski('#skF_6'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_149527,c_26])).

tff(c_150076,plain,
    ( r4_lattice3('#skF_5','#skF_6',k1_tarski('#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_32236,c_149792])).

tff(c_150077,plain,(
    r4_lattice3('#skF_5','#skF_6',k1_tarski('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_150076])).

tff(c_64,plain,(
    ! [A_66,C_72,B_70] :
      ( k15_lattice3(A_66,C_72) = B_70
      | ~ r4_lattice3(A_66,B_70,C_72)
      | ~ r2_hidden(B_70,C_72)
      | ~ m1_subset_1(B_70,u1_struct_0(A_66))
      | ~ l3_lattices(A_66)
      | ~ v4_lattice3(A_66)
      | ~ v10_lattices(A_66)
      | v2_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_150100,plain,
    ( k15_lattice3('#skF_5',k1_tarski('#skF_6')) = '#skF_6'
    | ~ r2_hidden('#skF_6',k1_tarski('#skF_6'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | ~ v4_lattice3('#skF_5')
    | ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_150077,c_64])).

tff(c_150274,plain,
    ( k15_lattice3('#skF_5',k1_tarski('#skF_6')) = '#skF_6'
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_72,c_34,c_150100])).

tff(c_150276,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_147,c_150274])).

tff(c_150277,plain,(
    k16_lattice3('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_6')) != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_150320,plain,(
    k16_lattice3('#skF_5',k1_tarski('#skF_6')) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_150317,c_150277])).

tff(c_172504,plain,(
    ! [A_103871,B_103872,C_103873] :
      ( r3_lattices(A_103871,B_103872,B_103872)
      | ~ m1_subset_1(C_103873,u1_struct_0(A_103871))
      | ~ m1_subset_1(B_103872,u1_struct_0(A_103871))
      | ~ l3_lattices(A_103871)
      | ~ v9_lattices(A_103871)
      | ~ v8_lattices(A_103871)
      | ~ v6_lattices(A_103871)
      | v2_struct_0(A_103871) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_172538,plain,(
    ! [B_103872] :
      ( r3_lattices('#skF_5',B_103872,B_103872)
      | ~ m1_subset_1(B_103872,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_72,c_172504])).

tff(c_172544,plain,(
    ! [B_103872] :
      ( r3_lattices('#skF_5',B_103872,B_103872)
      | ~ m1_subset_1(B_103872,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_172538])).

tff(c_172545,plain,(
    ! [B_103872] :
      ( r3_lattices('#skF_5',B_103872,B_103872)
      | ~ m1_subset_1(B_103872,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_172544])).

tff(c_172546,plain,(
    ~ v6_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_172545])).

tff(c_172553,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_172546])).

tff(c_172556,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_78,c_172553])).

tff(c_172558,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_172556])).

tff(c_172560,plain,(
    v6_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_172545])).

tff(c_172559,plain,(
    ! [B_103872] :
      ( ~ v8_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | r3_lattices('#skF_5',B_103872,B_103872)
      | ~ m1_subset_1(B_103872,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_172545])).

tff(c_173352,plain,(
    ~ v9_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_172559])).

tff(c_173359,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_2,c_173352])).

tff(c_173362,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_78,c_173359])).

tff(c_173364,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_173362])).

tff(c_173365,plain,(
    ! [B_103872] :
      ( ~ v8_lattices('#skF_5')
      | r3_lattices('#skF_5',B_103872,B_103872)
      | ~ m1_subset_1(B_103872,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_172559])).

tff(c_173415,plain,(
    ~ v8_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_173365])).

tff(c_173422,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_173415])).

tff(c_173425,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_78,c_173422])).

tff(c_173427,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_173425])).

tff(c_173429,plain,(
    v8_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_173365])).

tff(c_173366,plain,(
    v9_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_172559])).

tff(c_173512,plain,(
    ! [B_105500] :
      ( r3_lattices('#skF_5',B_105500,B_105500)
      | ~ m1_subset_1(B_105500,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_173365])).

tff(c_173603,plain,(
    r3_lattices('#skF_5','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_72,c_173512])).

tff(c_188371,plain,(
    ! [A_112591,B_112592,C_112593] :
      ( r1_lattices(A_112591,B_112592,C_112593)
      | ~ r3_lattices(A_112591,B_112592,C_112593)
      | ~ m1_subset_1(C_112593,u1_struct_0(A_112591))
      | ~ m1_subset_1(B_112592,u1_struct_0(A_112591))
      | ~ l3_lattices(A_112591)
      | ~ v9_lattices(A_112591)
      | ~ v8_lattices(A_112591)
      | ~ v6_lattices(A_112591)
      | v2_struct_0(A_112591) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_188391,plain,
    ( r1_lattices('#skF_5','#skF_6','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | ~ v9_lattices('#skF_5')
    | ~ v8_lattices('#skF_5')
    | ~ v6_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_173603,c_188371])).

tff(c_188427,plain,
    ( r1_lattices('#skF_5','#skF_6','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_172560,c_173429,c_173366,c_74,c_72,c_188391])).

tff(c_188428,plain,(
    r1_lattices('#skF_5','#skF_6','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_188427])).

tff(c_151128,plain,(
    ! [A_89554,B_89555,C_89556] :
      ( r2_hidden('#skF_1'(A_89554,B_89555,C_89556),C_89556)
      | r3_lattice3(A_89554,B_89555,C_89556)
      | ~ m1_subset_1(B_89555,u1_struct_0(A_89554))
      | ~ l3_lattices(A_89554)
      | v2_struct_0(A_89554) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_151149,plain,(
    ! [A_89554,B_89555,A_46] :
      ( '#skF_1'(A_89554,B_89555,k1_tarski(A_46)) = A_46
      | r3_lattice3(A_89554,B_89555,k1_tarski(A_46))
      | ~ m1_subset_1(B_89555,u1_struct_0(A_89554))
      | ~ l3_lattices(A_89554)
      | v2_struct_0(A_89554) ) ),
    inference(resolution,[status(thm)],[c_151128,c_32])).

tff(c_179848,plain,(
    ! [A_109124,C_109125,B_109126] :
      ( k16_lattice3(A_109124,C_109125) = B_109126
      | ~ r3_lattice3(A_109124,B_109126,C_109125)
      | ~ r2_hidden(B_109126,C_109125)
      | ~ m1_subset_1(B_109126,u1_struct_0(A_109124))
      | ~ l3_lattices(A_109124)
      | ~ v4_lattice3(A_109124)
      | ~ v10_lattices(A_109124)
      | v2_struct_0(A_109124) ) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_299757,plain,(
    ! [A_170999,A_171000,B_171001] :
      ( k16_lattice3(A_170999,k1_tarski(A_171000)) = B_171001
      | ~ r2_hidden(B_171001,k1_tarski(A_171000))
      | ~ v4_lattice3(A_170999)
      | ~ v10_lattices(A_170999)
      | '#skF_1'(A_170999,B_171001,k1_tarski(A_171000)) = A_171000
      | ~ m1_subset_1(B_171001,u1_struct_0(A_170999))
      | ~ l3_lattices(A_170999)
      | v2_struct_0(A_170999) ) ),
    inference(resolution,[status(thm)],[c_151149,c_179848])).

tff(c_314053,plain,(
    ! [A_188251,C_188252] :
      ( k16_lattice3(A_188251,k1_tarski(C_188252)) = C_188252
      | ~ v4_lattice3(A_188251)
      | ~ v10_lattices(A_188251)
      | '#skF_1'(A_188251,C_188252,k1_tarski(C_188252)) = C_188252
      | ~ m1_subset_1(C_188252,u1_struct_0(A_188251))
      | ~ l3_lattices(A_188251)
      | v2_struct_0(A_188251) ) ),
    inference(resolution,[status(thm)],[c_34,c_299757])).

tff(c_314256,plain,
    ( k16_lattice3('#skF_5',k1_tarski('#skF_6')) = '#skF_6'
    | ~ v4_lattice3('#skF_5')
    | ~ v10_lattices('#skF_5')
    | '#skF_1'('#skF_5','#skF_6',k1_tarski('#skF_6')) = '#skF_6'
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_314053])).

tff(c_314264,plain,
    ( k16_lattice3('#skF_5',k1_tarski('#skF_6')) = '#skF_6'
    | '#skF_1'('#skF_5','#skF_6',k1_tarski('#skF_6')) = '#skF_6'
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_78,c_76,c_314256])).

tff(c_314265,plain,(
    '#skF_1'('#skF_5','#skF_6',k1_tarski('#skF_6')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_150320,c_314264])).

tff(c_18,plain,(
    ! [A_2,B_14,C_20] :
      ( ~ r1_lattices(A_2,B_14,'#skF_1'(A_2,B_14,C_20))
      | r3_lattice3(A_2,B_14,C_20)
      | ~ m1_subset_1(B_14,u1_struct_0(A_2))
      | ~ l3_lattices(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_314323,plain,
    ( ~ r1_lattices('#skF_5','#skF_6','#skF_6')
    | r3_lattice3('#skF_5','#skF_6',k1_tarski('#skF_6'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_314265,c_18])).

tff(c_314705,plain,
    ( r3_lattice3('#skF_5','#skF_6',k1_tarski('#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_188428,c_314323])).

tff(c_314706,plain,(
    r3_lattice3('#skF_5','#skF_6',k1_tarski('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_314705])).

tff(c_66,plain,(
    ! [A_73,C_79,B_77] :
      ( k16_lattice3(A_73,C_79) = B_77
      | ~ r3_lattice3(A_73,B_77,C_79)
      | ~ r2_hidden(B_77,C_79)
      | ~ m1_subset_1(B_77,u1_struct_0(A_73))
      | ~ l3_lattices(A_73)
      | ~ v4_lattice3(A_73)
      | ~ v10_lattices(A_73)
      | v2_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_314748,plain,
    ( k16_lattice3('#skF_5',k1_tarski('#skF_6')) = '#skF_6'
    | ~ r2_hidden('#skF_6',k1_tarski('#skF_6'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | ~ v4_lattice3('#skF_5')
    | ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_314706,c_66])).

tff(c_314925,plain,
    ( k16_lattice3('#skF_5',k1_tarski('#skF_6')) = '#skF_6'
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_72,c_34,c_314748])).

tff(c_314927,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_150320,c_314925])).

%------------------------------------------------------------------------------
