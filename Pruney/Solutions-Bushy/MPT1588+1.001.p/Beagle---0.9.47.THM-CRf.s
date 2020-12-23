%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1588+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:07 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   54 (  96 expanded)
%              Number of leaves         :   24 (  50 expanded)
%              Depth                    :    7
%              Number of atoms          :  108 ( 422 expanded)
%              Number of equality atoms :    7 (  32 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_yellow_0 > r2_hidden > r1_yellow_0 > m1_yellow_0 > m1_subset_1 > v4_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k7_domain_1 > k1_yellow_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_yellow_0,type,(
    k1_yellow_0: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v4_yellow_0,type,(
    v4_yellow_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_domain_1,type,(
    k7_domain_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(r1_yellow_0,type,(
    r1_yellow_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(m1_yellow_0,type,(
    m1_yellow_0: ( $i * $i ) > $o )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_94,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v4_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v4_yellow_0(B,A)
              & m1_yellow_0(B,A) )
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(B))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(B))
                   => ( ( r1_yellow_0(A,k7_domain_1(u1_struct_0(B),C,D))
                        & r2_hidden(k1_yellow_0(A,k7_domain_1(u1_struct_0(B),C,D)),u1_struct_0(B)) )
                     => ( r1_yellow_0(B,k7_domain_1(u1_struct_0(B),C,D))
                        & k1_yellow_0(B,k7_domain_1(u1_struct_0(B),C,D)) = k1_yellow_0(A,k7_domain_1(u1_struct_0(B),C,D)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_yellow_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A)
        & m1_subset_1(C,A) )
     => m1_subset_1(k7_domain_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_domain_1)).

tff(f_59,axiom,(
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
             => ( ( r1_yellow_0(A,C)
                  & r2_hidden(k1_yellow_0(A,C),u1_struct_0(B)) )
               => ( r1_yellow_0(B,C)
                  & k1_yellow_0(B,C) = k1_yellow_0(A,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_yellow_0)).

tff(c_12,plain,(
    r2_hidden(k1_yellow_0('#skF_1',k7_domain_1(u1_struct_0('#skF_2'),'#skF_3','#skF_4')),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_8,plain,(
    ! [B_12,A_11] :
      ( ~ v1_xboole_0(B_12)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_35,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_12,c_8])).

tff(c_18,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_16,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] :
      ( m1_subset_1(k7_domain_1(A_1,B_2,C_3),k1_zfmisc_1(A_1))
      | ~ m1_subset_1(C_3,A_1)
      | ~ m1_subset_1(B_2,A_1)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_30,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_24,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_10,plain,
    ( k1_yellow_0('#skF_2',k7_domain_1(u1_struct_0('#skF_2'),'#skF_3','#skF_4')) != k1_yellow_0('#skF_1',k7_domain_1(u1_struct_0('#skF_2'),'#skF_3','#skF_4'))
    | ~ r1_yellow_0('#skF_2',k7_domain_1(u1_struct_0('#skF_2'),'#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_37,plain,(
    ~ r1_yellow_0('#skF_2',k7_domain_1(u1_struct_0('#skF_2'),'#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_10])).

tff(c_28,plain,(
    v4_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_26,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_22,plain,(
    v4_yellow_0('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_20,plain,(
    m1_yellow_0('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_14,plain,(
    r1_yellow_0('#skF_1',k7_domain_1(u1_struct_0('#skF_2'),'#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_38,plain,(
    ! [B_29,C_30,A_31] :
      ( r1_yellow_0(B_29,C_30)
      | ~ r2_hidden(k1_yellow_0(A_31,C_30),u1_struct_0(B_29))
      | ~ r1_yellow_0(A_31,C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(u1_struct_0(B_29)))
      | ~ m1_yellow_0(B_29,A_31)
      | ~ v4_yellow_0(B_29,A_31)
      | v2_struct_0(B_29)
      | ~ l1_orders_2(A_31)
      | ~ v4_orders_2(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_41,plain,
    ( r1_yellow_0('#skF_2',k7_domain_1(u1_struct_0('#skF_2'),'#skF_3','#skF_4'))
    | ~ r1_yellow_0('#skF_1',k7_domain_1(u1_struct_0('#skF_2'),'#skF_3','#skF_4'))
    | ~ m1_subset_1(k7_domain_1(u1_struct_0('#skF_2'),'#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_yellow_0('#skF_2','#skF_1')
    | ~ v4_yellow_0('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_38])).

tff(c_44,plain,
    ( r1_yellow_0('#skF_2',k7_domain_1(u1_struct_0('#skF_2'),'#skF_3','#skF_4'))
    | ~ m1_subset_1(k7_domain_1(u1_struct_0('#skF_2'),'#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_22,c_20,c_14,c_41])).

tff(c_45,plain,(
    ~ m1_subset_1(k7_domain_1(u1_struct_0('#skF_2'),'#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_24,c_37,c_44])).

tff(c_48,plain,
    ( ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2,c_45])).

tff(c_51,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_48])).

tff(c_53,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_51])).

tff(c_54,plain,(
    k1_yellow_0('#skF_2',k7_domain_1(u1_struct_0('#skF_2'),'#skF_3','#skF_4')) != k1_yellow_0('#skF_1',k7_domain_1(u1_struct_0('#skF_2'),'#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_10])).

tff(c_64,plain,(
    ! [B_35,C_36,A_37] :
      ( k1_yellow_0(B_35,C_36) = k1_yellow_0(A_37,C_36)
      | ~ r2_hidden(k1_yellow_0(A_37,C_36),u1_struct_0(B_35))
      | ~ r1_yellow_0(A_37,C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(u1_struct_0(B_35)))
      | ~ m1_yellow_0(B_35,A_37)
      | ~ v4_yellow_0(B_35,A_37)
      | v2_struct_0(B_35)
      | ~ l1_orders_2(A_37)
      | ~ v4_orders_2(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_67,plain,
    ( k1_yellow_0('#skF_2',k7_domain_1(u1_struct_0('#skF_2'),'#skF_3','#skF_4')) = k1_yellow_0('#skF_1',k7_domain_1(u1_struct_0('#skF_2'),'#skF_3','#skF_4'))
    | ~ r1_yellow_0('#skF_1',k7_domain_1(u1_struct_0('#skF_2'),'#skF_3','#skF_4'))
    | ~ m1_subset_1(k7_domain_1(u1_struct_0('#skF_2'),'#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_yellow_0('#skF_2','#skF_1')
    | ~ v4_yellow_0('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_64])).

tff(c_70,plain,
    ( k1_yellow_0('#skF_2',k7_domain_1(u1_struct_0('#skF_2'),'#skF_3','#skF_4')) = k1_yellow_0('#skF_1',k7_domain_1(u1_struct_0('#skF_2'),'#skF_3','#skF_4'))
    | ~ m1_subset_1(k7_domain_1(u1_struct_0('#skF_2'),'#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_22,c_20,c_14,c_67])).

tff(c_71,plain,(
    ~ m1_subset_1(k7_domain_1(u1_struct_0('#skF_2'),'#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_24,c_54,c_70])).

tff(c_74,plain,
    ( ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2,c_71])).

tff(c_77,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_74])).

tff(c_79,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_77])).

%------------------------------------------------------------------------------
