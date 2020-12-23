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
% DateTime   : Thu Dec  3 10:19:24 EST 2020

% Result     : Theorem 5.77s
% Output     : CNFRefutation 6.14s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 756 expanded)
%              Number of leaves         :   36 ( 290 expanded)
%              Depth                    :   18
%              Number of atoms          :  225 (2197 expanded)
%              Number of equality atoms :   32 ( 450 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff(k1_orders_2,type,(
    k1_orders_2: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(a_2_0_orders_2,type,(
    a_2_0_orders_2: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_138,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => k1_orders_2(A,k2_struct_0(A)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_orders_2)).

tff(f_97,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_62,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_48,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_50,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_93,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_orders_2(A,B) = a_2_0_orders_2(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_orders_2)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_124,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & v3_orders_2(B)
        & v4_orders_2(B)
        & v5_orders_2(B)
        & l1_orders_2(B)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B))) )
     => ( r2_hidden(A,a_2_0_orders_2(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & ! [E] :
                ( m1_subset_1(E,u1_struct_0(B))
               => ( r2_hidden(E,C)
                 => r2_orders_2(B,E,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_orders_2(A,B,C)
              <=> ( r1_orders_2(A,B,C)
                  & B != C ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).

tff(c_44,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_28,plain,(
    ! [A_19] :
      ( l1_struct_0(A_19)
      | ~ l1_orders_2(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_66,plain,(
    ! [A_37] :
      ( u1_struct_0(A_37) = k2_struct_0(A_37)
      | ~ l1_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_71,plain,(
    ! [A_38] :
      ( u1_struct_0(A_38) = k2_struct_0(A_38)
      | ~ l1_orders_2(A_38) ) ),
    inference(resolution,[status(thm)],[c_28,c_66])).

tff(c_75,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_71])).

tff(c_80,plain,(
    ! [A_39] :
      ( ~ v1_xboole_0(u1_struct_0(A_39))
      | ~ l1_struct_0(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_83,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_80])).

tff(c_84,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_83])).

tff(c_85,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_93,plain,(
    ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_85])).

tff(c_97,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_93])).

tff(c_98,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_12,plain,(
    ! [A_5] : k2_subset_1(A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_14,plain,(
    ! [A_6] : m1_subset_1(k2_subset_1(A_6),k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_53,plain,(
    ! [A_6] : m1_subset_1(A_6,k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_14])).

tff(c_50,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_48,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_46,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_2867,plain,(
    ! [A_283,B_284] :
      ( k1_orders_2(A_283,B_284) = a_2_0_orders_2(A_283,B_284)
      | ~ m1_subset_1(B_284,k1_zfmisc_1(u1_struct_0(A_283)))
      | ~ l1_orders_2(A_283)
      | ~ v5_orders_2(A_283)
      | ~ v4_orders_2(A_283)
      | ~ v3_orders_2(A_283)
      | v2_struct_0(A_283) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2878,plain,(
    ! [B_284] :
      ( k1_orders_2('#skF_4',B_284) = a_2_0_orders_2('#skF_4',B_284)
      | ~ m1_subset_1(B_284,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_2867])).

tff(c_2886,plain,(
    ! [B_284] :
      ( k1_orders_2('#skF_4',B_284) = a_2_0_orders_2('#skF_4',B_284)
      | ~ m1_subset_1(B_284,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_2878])).

tff(c_2889,plain,(
    ! [B_285] :
      ( k1_orders_2('#skF_4',B_285) = a_2_0_orders_2('#skF_4',B_285)
      | ~ m1_subset_1(B_285,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_2886])).

tff(c_2904,plain,(
    k1_orders_2('#skF_4',k2_struct_0('#skF_4')) = a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_53,c_2889])).

tff(c_42,plain,(
    k1_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_2905,plain,(
    a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2904,c_42])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_3594,plain,(
    ! [A_361,B_362,C_363] :
      ( '#skF_2'(A_361,B_362,C_363) = A_361
      | ~ r2_hidden(A_361,a_2_0_orders_2(B_362,C_363))
      | ~ m1_subset_1(C_363,k1_zfmisc_1(u1_struct_0(B_362)))
      | ~ l1_orders_2(B_362)
      | ~ v5_orders_2(B_362)
      | ~ v4_orders_2(B_362)
      | ~ v3_orders_2(B_362)
      | v2_struct_0(B_362) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_3846,plain,(
    ! [B_408,C_409] :
      ( '#skF_2'('#skF_1'(a_2_0_orders_2(B_408,C_409)),B_408,C_409) = '#skF_1'(a_2_0_orders_2(B_408,C_409))
      | ~ m1_subset_1(C_409,k1_zfmisc_1(u1_struct_0(B_408)))
      | ~ l1_orders_2(B_408)
      | ~ v5_orders_2(B_408)
      | ~ v4_orders_2(B_408)
      | ~ v3_orders_2(B_408)
      | v2_struct_0(B_408)
      | a_2_0_orders_2(B_408,C_409) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_3594])).

tff(c_3854,plain,(
    ! [C_409] :
      ( '#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4',C_409)),'#skF_4',C_409) = '#skF_1'(a_2_0_orders_2('#skF_4',C_409))
      | ~ m1_subset_1(C_409,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | a_2_0_orders_2('#skF_4',C_409) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_3846])).

tff(c_3861,plain,(
    ! [C_409] :
      ( '#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4',C_409)),'#skF_4',C_409) = '#skF_1'(a_2_0_orders_2('#skF_4',C_409))
      | ~ m1_subset_1(C_409,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | a_2_0_orders_2('#skF_4',C_409) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_3854])).

tff(c_3864,plain,(
    ! [C_410] :
      ( '#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4',C_410)),'#skF_4',C_410) = '#skF_1'(a_2_0_orders_2('#skF_4',C_410))
      | ~ m1_subset_1(C_410,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | a_2_0_orders_2('#skF_4',C_410) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_3861])).

tff(c_3873,plain,
    ( '#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),'#skF_4',k2_struct_0('#skF_4')) = '#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')))
    | a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_53,c_3864])).

tff(c_3880,plain,(
    '#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),'#skF_4',k2_struct_0('#skF_4')) = '#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_2905,c_3873])).

tff(c_3622,plain,(
    ! [A_372,B_373,C_374] :
      ( m1_subset_1('#skF_2'(A_372,B_373,C_374),u1_struct_0(B_373))
      | ~ r2_hidden(A_372,a_2_0_orders_2(B_373,C_374))
      | ~ m1_subset_1(C_374,k1_zfmisc_1(u1_struct_0(B_373)))
      | ~ l1_orders_2(B_373)
      | ~ v5_orders_2(B_373)
      | ~ v4_orders_2(B_373)
      | ~ v3_orders_2(B_373)
      | v2_struct_0(B_373) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_3632,plain,(
    ! [A_372,C_374] :
      ( m1_subset_1('#skF_2'(A_372,'#skF_4',C_374),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_372,a_2_0_orders_2('#skF_4',C_374))
      | ~ m1_subset_1(C_374,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_3622])).

tff(c_3637,plain,(
    ! [A_372,C_374] :
      ( m1_subset_1('#skF_2'(A_372,'#skF_4',C_374),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_372,a_2_0_orders_2('#skF_4',C_374))
      | ~ m1_subset_1(C_374,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_75,c_3632])).

tff(c_3638,plain,(
    ! [A_372,C_374] :
      ( m1_subset_1('#skF_2'(A_372,'#skF_4',C_374),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_372,a_2_0_orders_2('#skF_4',C_374))
      | ~ m1_subset_1(C_374,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_3637])).

tff(c_3884,plain,
    ( m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4'))
    | ~ r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')))
    | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3880,c_3638])).

tff(c_3891,plain,
    ( m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4'))
    | ~ r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_3884])).

tff(c_3896,plain,(
    ~ r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_3891])).

tff(c_3902,plain,(
    a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_3896])).

tff(c_3908,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2905,c_3902])).

tff(c_3909,plain,(
    m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_3891])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( r2_hidden(B_4,A_3)
      | ~ m1_subset_1(B_4,A_3)
      | v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_3910,plain,(
    r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_3891])).

tff(c_4007,plain,(
    ! [B_415,E_416,A_417,C_418] :
      ( r2_orders_2(B_415,E_416,'#skF_2'(A_417,B_415,C_418))
      | ~ r2_hidden(E_416,C_418)
      | ~ m1_subset_1(E_416,u1_struct_0(B_415))
      | ~ r2_hidden(A_417,a_2_0_orders_2(B_415,C_418))
      | ~ m1_subset_1(C_418,k1_zfmisc_1(u1_struct_0(B_415)))
      | ~ l1_orders_2(B_415)
      | ~ v5_orders_2(B_415)
      | ~ v4_orders_2(B_415)
      | ~ v3_orders_2(B_415)
      | v2_struct_0(B_415) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_4113,plain,(
    ! [B_424,E_425,A_426] :
      ( r2_orders_2(B_424,E_425,'#skF_2'(A_426,B_424,u1_struct_0(B_424)))
      | ~ r2_hidden(E_425,u1_struct_0(B_424))
      | ~ m1_subset_1(E_425,u1_struct_0(B_424))
      | ~ r2_hidden(A_426,a_2_0_orders_2(B_424,u1_struct_0(B_424)))
      | ~ l1_orders_2(B_424)
      | ~ v5_orders_2(B_424)
      | ~ v4_orders_2(B_424)
      | ~ v3_orders_2(B_424)
      | v2_struct_0(B_424) ) ),
    inference(resolution,[status(thm)],[c_53,c_4007])).

tff(c_4124,plain,(
    ! [E_425,A_426] :
      ( r2_orders_2('#skF_4',E_425,'#skF_2'(A_426,'#skF_4',k2_struct_0('#skF_4')))
      | ~ r2_hidden(E_425,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_425,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_426,a_2_0_orders_2('#skF_4',u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_4113])).

tff(c_4129,plain,(
    ! [E_425,A_426] :
      ( r2_orders_2('#skF_4',E_425,'#skF_2'(A_426,'#skF_4',k2_struct_0('#skF_4')))
      | ~ r2_hidden(E_425,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_425,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_426,a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_75,c_75,c_75,c_4124])).

tff(c_4193,plain,(
    ! [E_432,A_433] :
      ( r2_orders_2('#skF_4',E_432,'#skF_2'(A_433,'#skF_4',k2_struct_0('#skF_4')))
      | ~ r2_hidden(E_432,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_432,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_433,a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_4129])).

tff(c_4204,plain,(
    ! [E_432] :
      ( r2_orders_2('#skF_4',E_432,'#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))))
      | ~ r2_hidden(E_432,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_432,k2_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3880,c_4193])).

tff(c_4217,plain,(
    ! [E_434] :
      ( r2_orders_2('#skF_4',E_434,'#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))))
      | ~ r2_hidden(E_434,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_434,k2_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3910,c_4204])).

tff(c_22,plain,(
    ! [A_9,C_15] :
      ( ~ r2_orders_2(A_9,C_15,C_15)
      | ~ m1_subset_1(C_15,u1_struct_0(A_9))
      | ~ l1_orders_2(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_4225,plain,
    ( ~ m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4')
    | ~ r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_4217,c_22])).

tff(c_4235,plain,(
    ~ r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3909,c_44,c_3909,c_75,c_4225])).

tff(c_4238,plain,
    ( ~ m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4'))
    | v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6,c_4235])).

tff(c_4241,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3909,c_4238])).

tff(c_4243,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_4241])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:16:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.77/2.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.09/2.07  
% 6.09/2.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.09/2.07  %$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3
% 6.09/2.07  
% 6.09/2.07  %Foreground sorts:
% 6.09/2.07  
% 6.09/2.07  
% 6.09/2.07  %Background operators:
% 6.09/2.07  
% 6.09/2.07  
% 6.09/2.07  %Foreground operators:
% 6.09/2.07  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.09/2.07  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 6.09/2.07  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 6.09/2.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.09/2.07  tff(a_2_0_orders_2, type, a_2_0_orders_2: ($i * $i) > $i).
% 6.09/2.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.09/2.07  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.09/2.07  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 6.09/2.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.09/2.07  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.09/2.07  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 6.09/2.07  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 6.09/2.07  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.09/2.07  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 6.09/2.07  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 6.09/2.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.09/2.07  tff('#skF_4', type, '#skF_4': $i).
% 6.09/2.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.09/2.07  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 6.09/2.07  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 6.09/2.07  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.09/2.07  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 6.09/2.07  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 6.09/2.07  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.09/2.07  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.09/2.07  
% 6.14/2.09  tff(f_138, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k1_orders_2(A, k2_struct_0(A)) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_orders_2)).
% 6.14/2.09  tff(f_97, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 6.14/2.09  tff(f_54, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 6.14/2.09  tff(f_62, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 6.14/2.09  tff(f_48, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 6.14/2.09  tff(f_50, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 6.14/2.09  tff(f_93, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_orders_2(A, B) = a_2_0_orders_2(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_orders_2)).
% 6.14/2.09  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 6.14/2.09  tff(f_124, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_0_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, E, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_0_orders_2)).
% 6.14/2.09  tff(f_46, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 6.14/2.09  tff(f_77, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_orders_2)).
% 6.14/2.09  tff(c_44, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.14/2.09  tff(c_28, plain, (![A_19]: (l1_struct_0(A_19) | ~l1_orders_2(A_19))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.14/2.09  tff(c_52, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.14/2.09  tff(c_66, plain, (![A_37]: (u1_struct_0(A_37)=k2_struct_0(A_37) | ~l1_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.14/2.09  tff(c_71, plain, (![A_38]: (u1_struct_0(A_38)=k2_struct_0(A_38) | ~l1_orders_2(A_38))), inference(resolution, [status(thm)], [c_28, c_66])).
% 6.14/2.09  tff(c_75, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_44, c_71])).
% 6.14/2.09  tff(c_80, plain, (![A_39]: (~v1_xboole_0(u1_struct_0(A_39)) | ~l1_struct_0(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.14/2.09  tff(c_83, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_75, c_80])).
% 6.14/2.09  tff(c_84, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_52, c_83])).
% 6.14/2.09  tff(c_85, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_84])).
% 6.14/2.09  tff(c_93, plain, (~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_28, c_85])).
% 6.14/2.09  tff(c_97, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_93])).
% 6.14/2.09  tff(c_98, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_84])).
% 6.14/2.09  tff(c_12, plain, (![A_5]: (k2_subset_1(A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.14/2.09  tff(c_14, plain, (![A_6]: (m1_subset_1(k2_subset_1(A_6), k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.14/2.09  tff(c_53, plain, (![A_6]: (m1_subset_1(A_6, k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_14])).
% 6.14/2.09  tff(c_50, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.14/2.09  tff(c_48, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.14/2.09  tff(c_46, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.14/2.09  tff(c_2867, plain, (![A_283, B_284]: (k1_orders_2(A_283, B_284)=a_2_0_orders_2(A_283, B_284) | ~m1_subset_1(B_284, k1_zfmisc_1(u1_struct_0(A_283))) | ~l1_orders_2(A_283) | ~v5_orders_2(A_283) | ~v4_orders_2(A_283) | ~v3_orders_2(A_283) | v2_struct_0(A_283))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.14/2.09  tff(c_2878, plain, (![B_284]: (k1_orders_2('#skF_4', B_284)=a_2_0_orders_2('#skF_4', B_284) | ~m1_subset_1(B_284, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_75, c_2867])).
% 6.14/2.09  tff(c_2886, plain, (![B_284]: (k1_orders_2('#skF_4', B_284)=a_2_0_orders_2('#skF_4', B_284) | ~m1_subset_1(B_284, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_2878])).
% 6.14/2.09  tff(c_2889, plain, (![B_285]: (k1_orders_2('#skF_4', B_285)=a_2_0_orders_2('#skF_4', B_285) | ~m1_subset_1(B_285, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_52, c_2886])).
% 6.14/2.09  tff(c_2904, plain, (k1_orders_2('#skF_4', k2_struct_0('#skF_4'))=a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_53, c_2889])).
% 6.14/2.09  tff(c_42, plain, (k1_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.14/2.09  tff(c_2905, plain, (a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2904, c_42])).
% 6.14/2.09  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.14/2.09  tff(c_3594, plain, (![A_361, B_362, C_363]: ('#skF_2'(A_361, B_362, C_363)=A_361 | ~r2_hidden(A_361, a_2_0_orders_2(B_362, C_363)) | ~m1_subset_1(C_363, k1_zfmisc_1(u1_struct_0(B_362))) | ~l1_orders_2(B_362) | ~v5_orders_2(B_362) | ~v4_orders_2(B_362) | ~v3_orders_2(B_362) | v2_struct_0(B_362))), inference(cnfTransformation, [status(thm)], [f_124])).
% 6.14/2.09  tff(c_3846, plain, (![B_408, C_409]: ('#skF_2'('#skF_1'(a_2_0_orders_2(B_408, C_409)), B_408, C_409)='#skF_1'(a_2_0_orders_2(B_408, C_409)) | ~m1_subset_1(C_409, k1_zfmisc_1(u1_struct_0(B_408))) | ~l1_orders_2(B_408) | ~v5_orders_2(B_408) | ~v4_orders_2(B_408) | ~v3_orders_2(B_408) | v2_struct_0(B_408) | a_2_0_orders_2(B_408, C_409)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_3594])).
% 6.14/2.09  tff(c_3854, plain, (![C_409]: ('#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4', C_409)), '#skF_4', C_409)='#skF_1'(a_2_0_orders_2('#skF_4', C_409)) | ~m1_subset_1(C_409, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | a_2_0_orders_2('#skF_4', C_409)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_75, c_3846])).
% 6.14/2.09  tff(c_3861, plain, (![C_409]: ('#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4', C_409)), '#skF_4', C_409)='#skF_1'(a_2_0_orders_2('#skF_4', C_409)) | ~m1_subset_1(C_409, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | a_2_0_orders_2('#skF_4', C_409)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_3854])).
% 6.14/2.09  tff(c_3864, plain, (![C_410]: ('#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4', C_410)), '#skF_4', C_410)='#skF_1'(a_2_0_orders_2('#skF_4', C_410)) | ~m1_subset_1(C_410, k1_zfmisc_1(k2_struct_0('#skF_4'))) | a_2_0_orders_2('#skF_4', C_410)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_52, c_3861])).
% 6.14/2.09  tff(c_3873, plain, ('#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), '#skF_4', k2_struct_0('#skF_4'))='#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))) | a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_53, c_3864])).
% 6.14/2.09  tff(c_3880, plain, ('#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), '#skF_4', k2_struct_0('#skF_4'))='#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_2905, c_3873])).
% 6.14/2.09  tff(c_3622, plain, (![A_372, B_373, C_374]: (m1_subset_1('#skF_2'(A_372, B_373, C_374), u1_struct_0(B_373)) | ~r2_hidden(A_372, a_2_0_orders_2(B_373, C_374)) | ~m1_subset_1(C_374, k1_zfmisc_1(u1_struct_0(B_373))) | ~l1_orders_2(B_373) | ~v5_orders_2(B_373) | ~v4_orders_2(B_373) | ~v3_orders_2(B_373) | v2_struct_0(B_373))), inference(cnfTransformation, [status(thm)], [f_124])).
% 6.14/2.09  tff(c_3632, plain, (![A_372, C_374]: (m1_subset_1('#skF_2'(A_372, '#skF_4', C_374), k2_struct_0('#skF_4')) | ~r2_hidden(A_372, a_2_0_orders_2('#skF_4', C_374)) | ~m1_subset_1(C_374, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_75, c_3622])).
% 6.14/2.09  tff(c_3637, plain, (![A_372, C_374]: (m1_subset_1('#skF_2'(A_372, '#skF_4', C_374), k2_struct_0('#skF_4')) | ~r2_hidden(A_372, a_2_0_orders_2('#skF_4', C_374)) | ~m1_subset_1(C_374, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_75, c_3632])).
% 6.14/2.09  tff(c_3638, plain, (![A_372, C_374]: (m1_subset_1('#skF_2'(A_372, '#skF_4', C_374), k2_struct_0('#skF_4')) | ~r2_hidden(A_372, a_2_0_orders_2('#skF_4', C_374)) | ~m1_subset_1(C_374, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_52, c_3637])).
% 6.14/2.09  tff(c_3884, plain, (m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_3880, c_3638])).
% 6.14/2.09  tff(c_3891, plain, (m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_3884])).
% 6.14/2.09  tff(c_3896, plain, (~r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_3891])).
% 6.14/2.09  tff(c_3902, plain, (a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_3896])).
% 6.14/2.09  tff(c_3908, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2905, c_3902])).
% 6.14/2.09  tff(c_3909, plain, (m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_3891])).
% 6.14/2.09  tff(c_6, plain, (![B_4, A_3]: (r2_hidden(B_4, A_3) | ~m1_subset_1(B_4, A_3) | v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.14/2.09  tff(c_3910, plain, (r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_3891])).
% 6.14/2.09  tff(c_4007, plain, (![B_415, E_416, A_417, C_418]: (r2_orders_2(B_415, E_416, '#skF_2'(A_417, B_415, C_418)) | ~r2_hidden(E_416, C_418) | ~m1_subset_1(E_416, u1_struct_0(B_415)) | ~r2_hidden(A_417, a_2_0_orders_2(B_415, C_418)) | ~m1_subset_1(C_418, k1_zfmisc_1(u1_struct_0(B_415))) | ~l1_orders_2(B_415) | ~v5_orders_2(B_415) | ~v4_orders_2(B_415) | ~v3_orders_2(B_415) | v2_struct_0(B_415))), inference(cnfTransformation, [status(thm)], [f_124])).
% 6.14/2.09  tff(c_4113, plain, (![B_424, E_425, A_426]: (r2_orders_2(B_424, E_425, '#skF_2'(A_426, B_424, u1_struct_0(B_424))) | ~r2_hidden(E_425, u1_struct_0(B_424)) | ~m1_subset_1(E_425, u1_struct_0(B_424)) | ~r2_hidden(A_426, a_2_0_orders_2(B_424, u1_struct_0(B_424))) | ~l1_orders_2(B_424) | ~v5_orders_2(B_424) | ~v4_orders_2(B_424) | ~v3_orders_2(B_424) | v2_struct_0(B_424))), inference(resolution, [status(thm)], [c_53, c_4007])).
% 6.14/2.09  tff(c_4124, plain, (![E_425, A_426]: (r2_orders_2('#skF_4', E_425, '#skF_2'(A_426, '#skF_4', k2_struct_0('#skF_4'))) | ~r2_hidden(E_425, u1_struct_0('#skF_4')) | ~m1_subset_1(E_425, u1_struct_0('#skF_4')) | ~r2_hidden(A_426, a_2_0_orders_2('#skF_4', u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_75, c_4113])).
% 6.14/2.09  tff(c_4129, plain, (![E_425, A_426]: (r2_orders_2('#skF_4', E_425, '#skF_2'(A_426, '#skF_4', k2_struct_0('#skF_4'))) | ~r2_hidden(E_425, k2_struct_0('#skF_4')) | ~m1_subset_1(E_425, k2_struct_0('#skF_4')) | ~r2_hidden(A_426, a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_75, c_75, c_75, c_4124])).
% 6.14/2.09  tff(c_4193, plain, (![E_432, A_433]: (r2_orders_2('#skF_4', E_432, '#skF_2'(A_433, '#skF_4', k2_struct_0('#skF_4'))) | ~r2_hidden(E_432, k2_struct_0('#skF_4')) | ~m1_subset_1(E_432, k2_struct_0('#skF_4')) | ~r2_hidden(A_433, a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_52, c_4129])).
% 6.14/2.09  tff(c_4204, plain, (![E_432]: (r2_orders_2('#skF_4', E_432, '#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')))) | ~r2_hidden(E_432, k2_struct_0('#skF_4')) | ~m1_subset_1(E_432, k2_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_3880, c_4193])).
% 6.14/2.09  tff(c_4217, plain, (![E_434]: (r2_orders_2('#skF_4', E_434, '#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')))) | ~r2_hidden(E_434, k2_struct_0('#skF_4')) | ~m1_subset_1(E_434, k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_3910, c_4204])).
% 6.14/2.09  tff(c_22, plain, (![A_9, C_15]: (~r2_orders_2(A_9, C_15, C_15) | ~m1_subset_1(C_15, u1_struct_0(A_9)) | ~l1_orders_2(A_9))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.14/2.09  tff(c_4225, plain, (~m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_4217, c_22])).
% 6.14/2.09  tff(c_4235, plain, (~r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3909, c_44, c_3909, c_75, c_4225])).
% 6.14/2.09  tff(c_4238, plain, (~m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4')) | v1_xboole_0(k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_6, c_4235])).
% 6.14/2.09  tff(c_4241, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3909, c_4238])).
% 6.14/2.09  tff(c_4243, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_4241])).
% 6.14/2.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.14/2.09  
% 6.14/2.09  Inference rules
% 6.14/2.09  ----------------------
% 6.14/2.09  #Ref     : 0
% 6.14/2.09  #Sup     : 834
% 6.14/2.09  #Fact    : 0
% 6.14/2.09  #Define  : 0
% 6.14/2.09  #Split   : 19
% 6.14/2.09  #Chain   : 0
% 6.14/2.09  #Close   : 0
% 6.14/2.09  
% 6.14/2.09  Ordering : KBO
% 6.14/2.09  
% 6.14/2.09  Simplification rules
% 6.14/2.09  ----------------------
% 6.14/2.09  #Subsume      : 154
% 6.14/2.09  #Demod        : 857
% 6.14/2.09  #Tautology    : 202
% 6.14/2.09  #SimpNegUnit  : 187
% 6.14/2.09  #BackRed      : 15
% 6.14/2.09  
% 6.14/2.09  #Partial instantiations: 0
% 6.14/2.09  #Strategies tried      : 1
% 6.14/2.09  
% 6.14/2.09  Timing (in seconds)
% 6.14/2.09  ----------------------
% 6.14/2.09  Preprocessing        : 0.30
% 6.14/2.09  Parsing              : 0.15
% 6.14/2.09  CNF conversion       : 0.02
% 6.14/2.09  Main loop            : 1.11
% 6.14/2.09  Inferencing          : 0.40
% 6.14/2.09  Reduction            : 0.32
% 6.14/2.09  Demodulation         : 0.21
% 6.14/2.09  BG Simplification    : 0.05
% 6.14/2.09  Subsumption          : 0.26
% 6.14/2.09  Abstraction          : 0.07
% 6.14/2.09  MUC search           : 0.00
% 6.14/2.09  Cooper               : 0.00
% 6.14/2.09  Total                : 1.44
% 6.14/2.09  Index Insertion      : 0.00
% 6.14/2.09  Index Deletion       : 0.00
% 6.14/2.09  Index Matching       : 0.00
% 6.14/2.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
