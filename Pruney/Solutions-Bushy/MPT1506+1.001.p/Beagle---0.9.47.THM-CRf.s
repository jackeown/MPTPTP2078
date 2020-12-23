%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1506+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:58 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   40 (  52 expanded)
%              Number of leaves         :   23 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   70 ( 136 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_lattices > r3_lattice3 > r2_hidden > m1_subset_1 > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > k15_lattice3 > a_2_1_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(a_2_1_lattice3,type,(
    a_2_1_lattice3: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_lattice3,type,(
    v4_lattice3: $i > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(r3_lattice3,type,(
    r3_lattice3: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v4_lattice3(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( r3_lattice3(A,B,C)
               => r3_lattices(A,B,k16_lattice3(A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_lattice3)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & l3_lattices(B) )
     => ( r2_hidden(A,a_2_1_lattice3(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & r3_lattice3(B,D,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_lattice3)).

tff(f_32,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ! [B] : k16_lattice3(A,B) = k15_lattice3(A,a_2_1_lattice3(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d22_lattice3)).

tff(f_65,axiom,(
    ! [A] :
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

tff(c_28,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_22,plain,(
    l3_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_18,plain,(
    r3_lattice3('#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_4,plain,(
    ! [D_9,B_5,C_6] :
      ( r2_hidden(D_9,a_2_1_lattice3(B_5,C_6))
      | ~ r3_lattice3(B_5,D_9,C_6)
      | ~ m1_subset_1(D_9,u1_struct_0(B_5))
      | ~ l3_lattices(B_5)
      | v2_struct_0(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_26,plain,(
    v10_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_24,plain,(
    v4_lattice3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2,plain,(
    ! [A_1,B_3] :
      ( k15_lattice3(A_1,a_2_1_lattice3(A_1,B_3)) = k16_lattice3(A_1,B_3)
      | ~ l3_lattices(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_73,plain,(
    ! [A_41,B_42,C_43] :
      ( r3_lattices(A_41,B_42,k15_lattice3(A_41,C_43))
      | ~ r2_hidden(B_42,C_43)
      | ~ m1_subset_1(B_42,u1_struct_0(A_41))
      | ~ l3_lattices(A_41)
      | ~ v4_lattice3(A_41)
      | ~ v10_lattices(A_41)
      | v2_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_77,plain,(
    ! [A_44,B_45,B_46] :
      ( r3_lattices(A_44,B_45,k16_lattice3(A_44,B_46))
      | ~ r2_hidden(B_45,a_2_1_lattice3(A_44,B_46))
      | ~ m1_subset_1(B_45,u1_struct_0(A_44))
      | ~ l3_lattices(A_44)
      | ~ v4_lattice3(A_44)
      | ~ v10_lattices(A_44)
      | v2_struct_0(A_44)
      | ~ l3_lattices(A_44)
      | v2_struct_0(A_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_73])).

tff(c_16,plain,(
    ~ r3_lattices('#skF_2','#skF_3',k16_lattice3('#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_80,plain,
    ( ~ r2_hidden('#skF_3',a_2_1_lattice3('#skF_2','#skF_4'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ v4_lattice3('#skF_2')
    | ~ v10_lattices('#skF_2')
    | ~ l3_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_77,c_16])).

tff(c_83,plain,
    ( ~ r2_hidden('#skF_3',a_2_1_lattice3('#skF_2','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_26,c_24,c_20,c_80])).

tff(c_84,plain,(
    ~ r2_hidden('#skF_3',a_2_1_lattice3('#skF_2','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_83])).

tff(c_87,plain,
    ( ~ r3_lattice3('#skF_2','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l3_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_84])).

tff(c_90,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_18,c_87])).

tff(c_92,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_90])).

%------------------------------------------------------------------------------
