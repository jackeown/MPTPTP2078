%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1589+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:07 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   43 (  57 expanded)
%              Number of leaves         :   24 (  36 expanded)
%              Depth                    :    7
%              Number of atoms          :   75 ( 221 expanded)
%              Number of equality atoms :    6 (  18 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_yellow_0 > r2_yellow_0 > r2_hidden > r1_yellow_0 > m1_yellow_0 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v3_lattice3 > v2_struct_0 > l1_orders_2 > k2_yellow_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v4_yellow_0,type,(
    v4_yellow_0: ( $i * $i ) > $o )).

tff(v3_lattice3,type,(
    v3_lattice3: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(r2_yellow_0,type,(
    r2_yellow_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k2_yellow_0,type,(
    k2_yellow_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(r1_yellow_0,type,(
    r1_yellow_0: ( $i * $i ) > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(m1_yellow_0,type,(
    m1_yellow_0: ( $i * $i ) > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_93,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & v3_lattice3(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v4_yellow_0(B,A)
              & m1_yellow_0(B,A) )
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
               => ( r2_hidden(k2_yellow_0(A,C),u1_struct_0(B))
                 => k2_yellow_0(B,C) = k2_yellow_0(A,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_yellow_0)).

tff(f_38,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v3_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( r1_yellow_0(A,B)
          & r2_yellow_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_yellow_0)).

tff(f_64,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v4_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_yellow_0(B,A)
            & m1_yellow_0(B,A) )
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => ( ( r2_yellow_0(A,C)
                  & r2_hidden(k2_yellow_0(A,C),u1_struct_0(B)) )
               => ( r2_yellow_0(B,C)
                  & k2_yellow_0(B,C) = k2_yellow_0(A,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_yellow_0)).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_26,plain,(
    v5_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_24,plain,(
    v3_lattice3('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_22,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_4,plain,(
    ! [A_1,B_3] :
      ( r2_yellow_0(A_1,B_3)
      | ~ l1_orders_2(A_1)
      | ~ v3_lattice3(A_1)
      | ~ v5_orders_2(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_20,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_10,plain,(
    k2_yellow_0('#skF_2','#skF_3') != k2_yellow_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_28,plain,(
    v4_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_18,plain,(
    v4_yellow_0('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_16,plain,(
    m1_yellow_0('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_14,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_12,plain,(
    r2_hidden(k2_yellow_0('#skF_1','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_43,plain,(
    ! [B_22,C_23,A_24] :
      ( k2_yellow_0(B_22,C_23) = k2_yellow_0(A_24,C_23)
      | ~ r2_hidden(k2_yellow_0(A_24,C_23),u1_struct_0(B_22))
      | ~ r2_yellow_0(A_24,C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(u1_struct_0(B_22)))
      | ~ m1_yellow_0(B_22,A_24)
      | ~ v4_yellow_0(B_22,A_24)
      | v2_struct_0(B_22)
      | ~ l1_orders_2(A_24)
      | ~ v4_orders_2(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_46,plain,
    ( k2_yellow_0('#skF_2','#skF_3') = k2_yellow_0('#skF_1','#skF_3')
    | ~ r2_yellow_0('#skF_1','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_yellow_0('#skF_2','#skF_1')
    | ~ v4_yellow_0('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_43])).

tff(c_49,plain,
    ( k2_yellow_0('#skF_2','#skF_3') = k2_yellow_0('#skF_1','#skF_3')
    | ~ r2_yellow_0('#skF_1','#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_22,c_18,c_16,c_14,c_46])).

tff(c_50,plain,(
    ~ r2_yellow_0('#skF_1','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_20,c_10,c_49])).

tff(c_53,plain,
    ( ~ l1_orders_2('#skF_1')
    | ~ v3_lattice3('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_50])).

tff(c_56,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_53])).

tff(c_58,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_56])).

%------------------------------------------------------------------------------
