%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1184+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:33 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   54 (  80 expanded)
%              Number of leaves         :   29 (  42 expanded)
%              Depth                    :    8
%              Number of atoms          :   73 ( 200 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v6_orders_2 > r8_relat_2 > r7_relat_2 > r6_relat_2 > r4_relat_2 > r3_orders_1 > r1_relat_2 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_relat_1 > l1_orders_2 > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(r3_orders_1,type,(
    r3_orders_1: ( $i * $i ) > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r4_relat_2,type,(
    r4_relat_2: ( $i * $i ) > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r6_relat_2,type,(
    r6_relat_2: ( $i * $i ) > $o )).

tff(r1_relat_2,type,(
    r1_relat_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(r7_relat_2,type,(
    r7_relat_2: ( $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(r8_relat_2,type,(
    r8_relat_2: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( r3_orders_1(u1_orders_2(A),B)
             => ( v6_orders_2(B,A)
                & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_orders_2)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r3_orders_1(A,B)
        <=> ( r1_relat_2(A,B)
            & r8_relat_2(A,B)
            & r4_relat_2(A,B)
            & r6_relat_2(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_orders_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r7_relat_2(B,A)
      <=> ( r1_relat_2(B,A)
          & r6_relat_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_orders_1)).

tff(f_37,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v6_orders_2(B,A)
          <=> r7_relat_2(u1_orders_2(A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_orders_2)).

tff(c_32,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_64,plain,(
    ! [A_31] :
      ( m1_subset_1(u1_orders_2(A_31),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_31),u1_struct_0(A_31))))
      | ~ l1_orders_2(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [C_3,A_1,B_2] :
      ( v1_relat_1(C_3)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_81,plain,(
    ! [A_34] :
      ( v1_relat_1(u1_orders_2(A_34))
      | ~ l1_orders_2(A_34) ) ),
    inference(resolution,[status(thm)],[c_64,c_2])).

tff(c_28,plain,(
    r3_orders_1(u1_orders_2('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_46,plain,(
    ! [A_20,B_21] :
      ( r1_relat_2(A_20,B_21)
      | ~ r3_orders_1(A_20,B_21)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_50,plain,
    ( r1_relat_2(u1_orders_2('#skF_1'),'#skF_2')
    | ~ v1_relat_1(u1_orders_2('#skF_1')) ),
    inference(resolution,[status(thm)],[c_28,c_46])).

tff(c_51,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_84,plain,(
    ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_81,c_51])).

tff(c_88,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_84])).

tff(c_90,plain,(
    v1_relat_1(u1_orders_2('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_10,plain,(
    ! [A_7,B_9] :
      ( r6_relat_2(A_7,B_9)
      | ~ r3_orders_1(A_7,B_9)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_89,plain,(
    r1_relat_2(u1_orders_2('#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_20,plain,(
    ! [B_12,A_11] :
      ( r7_relat_2(B_12,A_11)
      | ~ r6_relat_2(B_12,A_11)
      | ~ r1_relat_2(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_26,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v6_orders_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_42,plain,(
    ~ v6_orders_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26])).

tff(c_108,plain,(
    ! [B_45,A_46] :
      ( v6_orders_2(B_45,A_46)
      | ~ r7_relat_2(u1_orders_2(A_46),B_45)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ l1_orders_2(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_111,plain,
    ( v6_orders_2('#skF_2','#skF_1')
    | ~ r7_relat_2(u1_orders_2('#skF_1'),'#skF_2')
    | ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_108])).

tff(c_114,plain,
    ( v6_orders_2('#skF_2','#skF_1')
    | ~ r7_relat_2(u1_orders_2('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_111])).

tff(c_115,plain,(
    ~ r7_relat_2(u1_orders_2('#skF_1'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_114])).

tff(c_118,plain,
    ( ~ r6_relat_2(u1_orders_2('#skF_1'),'#skF_2')
    | ~ r1_relat_2(u1_orders_2('#skF_1'),'#skF_2')
    | ~ v1_relat_1(u1_orders_2('#skF_1')) ),
    inference(resolution,[status(thm)],[c_20,c_115])).

tff(c_121,plain,(
    ~ r6_relat_2(u1_orders_2('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_89,c_118])).

tff(c_124,plain,
    ( ~ r3_orders_1(u1_orders_2('#skF_1'),'#skF_2')
    | ~ v1_relat_1(u1_orders_2('#skF_1')) ),
    inference(resolution,[status(thm)],[c_10,c_121])).

tff(c_128,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_28,c_124])).

%------------------------------------------------------------------------------
