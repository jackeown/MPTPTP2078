%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1199+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:34 EST 2020

% Result     : Theorem 1.77s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   51 (  98 expanded)
%              Number of leaves         :   18 (  45 expanded)
%              Depth                    :    8
%              Number of atoms          :  105 ( 347 expanded)
%              Number of equality atoms :   29 (  58 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_lattices > m1_subset_1 > v4_lattices > v2_struct_0 > l2_lattices > k3_lattices > k1_lattices > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k3_lattices,type,(
    k3_lattices: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(l2_lattices,type,(
    l2_lattices: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_lattices,type,(
    k1_lattices: ( $i * $i * $i ) > $i )).

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

tff(v4_lattices,type,(
    v4_lattices: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v4_lattices(A)
          & l2_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( ( r1_lattices(A,B,C)
                    & r1_lattices(A,C,B) )
                 => B = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_lattices)).

tff(f_52,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l2_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_lattices(A,B,C)
              <=> k1_lattices(A,B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattices)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v4_lattices(A)
        & l2_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k3_lattices(A,B,C) = k1_lattices(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_lattices)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v4_lattices(A)
        & l2_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k3_lattices(A,B,C) = k3_lattices(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_lattices)).

tff(c_10,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_24,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_20,plain,(
    l2_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_16,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_18,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_12,plain,(
    r1_lattices('#skF_1','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_60,plain,(
    ! [A_23,B_24,C_25] :
      ( k1_lattices(A_23,B_24,C_25) = C_25
      | ~ r1_lattices(A_23,B_24,C_25)
      | ~ m1_subset_1(C_25,u1_struct_0(A_23))
      | ~ m1_subset_1(B_24,u1_struct_0(A_23))
      | ~ l2_lattices(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_62,plain,
    ( k1_lattices('#skF_1','#skF_3','#skF_2') = '#skF_2'
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
    | ~ l2_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_60])).

tff(c_67,plain,
    ( k1_lattices('#skF_1','#skF_3','#skF_2') = '#skF_2'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_16,c_18,c_62])).

tff(c_68,plain,(
    k1_lattices('#skF_1','#skF_3','#skF_2') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_67])).

tff(c_22,plain,(
    v4_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_81,plain,(
    ! [A_26,B_27,C_28] :
      ( k3_lattices(A_26,B_27,C_28) = k1_lattices(A_26,B_27,C_28)
      | ~ m1_subset_1(C_28,u1_struct_0(A_26))
      | ~ m1_subset_1(B_27,u1_struct_0(A_26))
      | ~ l2_lattices(A_26)
      | ~ v4_lattices(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_85,plain,(
    ! [B_27] :
      ( k3_lattices('#skF_1',B_27,'#skF_2') = k1_lattices('#skF_1',B_27,'#skF_2')
      | ~ m1_subset_1(B_27,u1_struct_0('#skF_1'))
      | ~ l2_lattices('#skF_1')
      | ~ v4_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_18,c_81])).

tff(c_92,plain,(
    ! [B_27] :
      ( k3_lattices('#skF_1',B_27,'#skF_2') = k1_lattices('#skF_1',B_27,'#skF_2')
      | ~ m1_subset_1(B_27,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_85])).

tff(c_112,plain,(
    ! [B_30] :
      ( k3_lattices('#skF_1',B_30,'#skF_2') = k1_lattices('#skF_1',B_30,'#skF_2')
      | ~ m1_subset_1(B_30,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_92])).

tff(c_115,plain,(
    k3_lattices('#skF_1','#skF_3','#skF_2') = k1_lattices('#skF_1','#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_112])).

tff(c_120,plain,(
    k3_lattices('#skF_1','#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_115])).

tff(c_14,plain,(
    r1_lattices('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_64,plain,
    ( k1_lattices('#skF_1','#skF_2','#skF_3') = '#skF_3'
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l2_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_60])).

tff(c_71,plain,
    ( k1_lattices('#skF_1','#skF_2','#skF_3') = '#skF_3'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_16,c_64])).

tff(c_72,plain,(
    k1_lattices('#skF_1','#skF_2','#skF_3') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_71])).

tff(c_83,plain,(
    ! [B_27] :
      ( k3_lattices('#skF_1',B_27,'#skF_3') = k1_lattices('#skF_1',B_27,'#skF_3')
      | ~ m1_subset_1(B_27,u1_struct_0('#skF_1'))
      | ~ l2_lattices('#skF_1')
      | ~ v4_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_16,c_81])).

tff(c_88,plain,(
    ! [B_27] :
      ( k3_lattices('#skF_1',B_27,'#skF_3') = k1_lattices('#skF_1',B_27,'#skF_3')
      | ~ m1_subset_1(B_27,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_83])).

tff(c_94,plain,(
    ! [B_29] :
      ( k3_lattices('#skF_1',B_29,'#skF_3') = k1_lattices('#skF_1',B_29,'#skF_3')
      | ~ m1_subset_1(B_29,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_88])).

tff(c_100,plain,(
    k3_lattices('#skF_1','#skF_2','#skF_3') = k1_lattices('#skF_1','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_94])).

tff(c_103,plain,(
    k3_lattices('#skF_1','#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_100])).

tff(c_130,plain,(
    ! [A_31,C_32,B_33] :
      ( k3_lattices(A_31,C_32,B_33) = k3_lattices(A_31,B_33,C_32)
      | ~ m1_subset_1(C_32,u1_struct_0(A_31))
      | ~ m1_subset_1(B_33,u1_struct_0(A_31))
      | ~ l2_lattices(A_31)
      | ~ v4_lattices(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_132,plain,(
    ! [B_33] :
      ( k3_lattices('#skF_1',B_33,'#skF_3') = k3_lattices('#skF_1','#skF_3',B_33)
      | ~ m1_subset_1(B_33,u1_struct_0('#skF_1'))
      | ~ l2_lattices('#skF_1')
      | ~ v4_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_16,c_130])).

tff(c_137,plain,(
    ! [B_33] :
      ( k3_lattices('#skF_1',B_33,'#skF_3') = k3_lattices('#skF_1','#skF_3',B_33)
      | ~ m1_subset_1(B_33,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_132])).

tff(c_143,plain,(
    ! [B_34] :
      ( k3_lattices('#skF_1',B_34,'#skF_3') = k3_lattices('#skF_1','#skF_3',B_34)
      | ~ m1_subset_1(B_34,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_137])).

tff(c_149,plain,(
    k3_lattices('#skF_1','#skF_2','#skF_3') = k3_lattices('#skF_1','#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_143])).

tff(c_153,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_103,c_149])).

tff(c_155,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_153])).

%------------------------------------------------------------------------------
