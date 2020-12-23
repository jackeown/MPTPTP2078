%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:15 EST 2020

% Result     : Theorem 5.76s
% Output     : CNFRefutation 5.76s
% Verified   : 
% Statistics : Number of formulae       :  179 (4794 expanded)
%              Number of leaves         :   50 (1691 expanded)
%              Depth                    :   21
%              Number of atoms          :  303 (14595 expanded)
%              Number of equality atoms :   83 (4776 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_179,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_struct_0(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( ( k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                    & v2_funct_1(C) )
                 => ( k1_relset_1(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) = k2_struct_0(B)
                    & k2_relset_1(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) = k2_struct_0(A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).

tff(f_123,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_131,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_119,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_143,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_155,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_tops_2(A,B,C))
        & v1_funct_2(k2_tops_2(A,B,C),B,A)
        & m1_subset_1(k2_tops_2(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_111,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_80,plain,(
    l1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_131,plain,(
    ! [A_56] :
      ( u1_struct_0(A_56) = k2_struct_0(A_56)
      | ~ l1_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_138,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_131])).

tff(c_84,plain,(
    l1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_139,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_131])).

tff(c_74,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_2097,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_139,c_74])).

tff(c_3172,plain,(
    ! [C_553,A_554,B_555] :
      ( v1_relat_1(C_553)
      | ~ m1_subset_1(C_553,k1_zfmisc_1(k2_zfmisc_1(A_554,B_555))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_3180,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2097,c_3172])).

tff(c_78,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_70,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_24,plain,(
    ! [A_16] :
      ( k2_relat_1(k2_funct_1(A_16)) = k1_relat_1(A_16)
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_3373,plain,(
    ! [A_590,B_591,C_592] :
      ( k2_relset_1(A_590,B_591,C_592) = k2_relat_1(C_592)
      | ~ m1_subset_1(C_592,k1_zfmisc_1(k2_zfmisc_1(A_590,B_591))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_3383,plain,(
    k2_relset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'),'#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2097,c_3373])).

tff(c_72,plain,(
    k2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') = k2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_150,plain,(
    k2_relset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'),'#skF_5') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_138,c_72])).

tff(c_3398,plain,(
    k2_struct_0('#skF_4') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3383,c_150])).

tff(c_82,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_155,plain,(
    ! [A_57] :
      ( ~ v1_xboole_0(u1_struct_0(A_57))
      | ~ l1_struct_0(A_57)
      | v2_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_161,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_155])).

tff(c_165,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_161])).

tff(c_166,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_165])).

tff(c_3408,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3398,c_166])).

tff(c_3206,plain,(
    ! [C_566,A_567,B_568] :
      ( v4_relat_1(C_566,A_567)
      | ~ m1_subset_1(C_566,k1_zfmisc_1(k2_zfmisc_1(A_567,B_568))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_3216,plain,(
    v4_relat_1('#skF_5',k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2097,c_3206])).

tff(c_3291,plain,(
    ! [B_581,A_582] :
      ( k1_relat_1(B_581) = A_582
      | ~ v1_partfun1(B_581,A_582)
      | ~ v4_relat_1(B_581,A_582)
      | ~ v1_relat_1(B_581) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_3294,plain,
    ( k2_struct_0('#skF_3') = k1_relat_1('#skF_5')
    | ~ v1_partfun1('#skF_5',k2_struct_0('#skF_3'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_3216,c_3291])).

tff(c_3297,plain,
    ( k2_struct_0('#skF_3') = k1_relat_1('#skF_5')
    | ~ v1_partfun1('#skF_5',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3180,c_3294])).

tff(c_3298,plain,(
    ~ v1_partfun1('#skF_5',k2_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_3297])).

tff(c_76,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_140,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_76])).

tff(c_149,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_3'),k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_140])).

tff(c_3409,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_3'),k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3398,c_149])).

tff(c_3407,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'),k2_relat_1('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3398,c_2097])).

tff(c_3543,plain,(
    ! [C_630,A_631,B_632] :
      ( v1_partfun1(C_630,A_631)
      | ~ v1_funct_2(C_630,A_631,B_632)
      | ~ v1_funct_1(C_630)
      | ~ m1_subset_1(C_630,k1_zfmisc_1(k2_zfmisc_1(A_631,B_632)))
      | v1_xboole_0(B_632) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_3546,plain,
    ( v1_partfun1('#skF_5',k2_struct_0('#skF_3'))
    | ~ v1_funct_2('#skF_5',k2_struct_0('#skF_3'),k2_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0(k2_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_3407,c_3543])).

tff(c_3555,plain,
    ( v1_partfun1('#skF_5',k2_struct_0('#skF_3'))
    | v1_xboole_0(k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_3409,c_3546])).

tff(c_3557,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3408,c_3298,c_3555])).

tff(c_3558,plain,(
    k2_struct_0('#skF_3') = k1_relat_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_3297])).

tff(c_3563,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),k2_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3558,c_2097])).

tff(c_3726,plain,(
    ! [A_648,B_649,C_650] :
      ( k2_relset_1(A_648,B_649,C_650) = k2_relat_1(C_650)
      | ~ m1_subset_1(C_650,k1_zfmisc_1(k2_zfmisc_1(A_648,B_649))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_3736,plain,(
    k2_relset_1(k1_relat_1('#skF_5'),k2_struct_0('#skF_4'),'#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_3563,c_3726])).

tff(c_3565,plain,(
    k2_relset_1(k1_relat_1('#skF_5'),k2_struct_0('#skF_4'),'#skF_5') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3558,c_150])).

tff(c_3737,plain,(
    k2_struct_0('#skF_4') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3736,c_3565])).

tff(c_3566,plain,(
    v1_funct_2('#skF_5',k1_relat_1('#skF_5'),k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3558,c_149])).

tff(c_3745,plain,(
    v1_funct_2('#skF_5',k1_relat_1('#skF_5'),k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3737,c_3566])).

tff(c_3744,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3737,c_3563])).

tff(c_3742,plain,(
    k2_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3737,c_3736])).

tff(c_4041,plain,(
    ! [A_710,B_711,C_712] :
      ( k2_tops_2(A_710,B_711,C_712) = k2_funct_1(C_712)
      | ~ v2_funct_1(C_712)
      | k2_relset_1(A_710,B_711,C_712) != B_711
      | ~ m1_subset_1(C_712,k1_zfmisc_1(k2_zfmisc_1(A_710,B_711)))
      | ~ v1_funct_2(C_712,A_710,B_711)
      | ~ v1_funct_1(C_712) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_4047,plain,
    ( k2_tops_2(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5') = k2_funct_1('#skF_5')
    | ~ v2_funct_1('#skF_5')
    | k2_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5') != k2_relat_1('#skF_5')
    | ~ v1_funct_2('#skF_5',k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_3744,c_4041])).

tff(c_4057,plain,(
    k2_tops_2(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5') = k2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_3745,c_3742,c_70,c_4047])).

tff(c_62,plain,(
    ! [A_40,B_41,C_42] :
      ( m1_subset_1(k2_tops_2(A_40,B_41,C_42),k1_zfmisc_1(k2_zfmisc_1(B_41,A_40)))
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41)))
      | ~ v1_funct_2(C_42,A_40,B_41)
      | ~ v1_funct_1(C_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_4066,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_5'),k1_relat_1('#skF_5'))))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))))
    | ~ v1_funct_2('#skF_5',k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_4057,c_62])).

tff(c_4070,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_5'),k1_relat_1('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_3745,c_3744,c_4066])).

tff(c_34,plain,(
    ! [A_23,B_24,C_25] :
      ( k2_relset_1(A_23,B_24,C_25) = k2_relat_1(C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_4129,plain,(
    k2_relset_1(k2_relat_1('#skF_5'),k1_relat_1('#skF_5'),k2_funct_1('#skF_5')) = k2_relat_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_4070,c_34])).

tff(c_20,plain,(
    ! [A_14] :
      ( v1_xboole_0(k2_relat_1(A_14))
      | ~ v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2289,plain,(
    ! [A_417,B_418,C_419] :
      ( k2_relset_1(A_417,B_418,C_419) = k2_relat_1(C_419)
      | ~ m1_subset_1(C_419,k1_zfmisc_1(k2_zfmisc_1(A_417,B_418))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2299,plain,(
    k2_relset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'),'#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2097,c_2289])).

tff(c_2300,plain,(
    k2_struct_0('#skF_4') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2299,c_150])).

tff(c_2309,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2300,c_166])).

tff(c_2130,plain,(
    ! [C_385,A_386,B_387] :
      ( v1_relat_1(C_385)
      | ~ m1_subset_1(C_385,k1_zfmisc_1(k2_zfmisc_1(A_386,B_387))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2138,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2097,c_2130])).

tff(c_2160,plain,(
    ! [C_398,A_399,B_400] :
      ( v4_relat_1(C_398,A_399)
      | ~ m1_subset_1(C_398,k1_zfmisc_1(k2_zfmisc_1(A_399,B_400))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2170,plain,(
    v4_relat_1('#skF_5',k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2097,c_2160])).

tff(c_2210,plain,(
    ! [B_408,A_409] :
      ( k1_relat_1(B_408) = A_409
      | ~ v1_partfun1(B_408,A_409)
      | ~ v4_relat_1(B_408,A_409)
      | ~ v1_relat_1(B_408) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_2213,plain,
    ( k2_struct_0('#skF_3') = k1_relat_1('#skF_5')
    | ~ v1_partfun1('#skF_5',k2_struct_0('#skF_3'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2170,c_2210])).

tff(c_2216,plain,
    ( k2_struct_0('#skF_3') = k1_relat_1('#skF_5')
    | ~ v1_partfun1('#skF_5',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2138,c_2213])).

tff(c_2250,plain,(
    ~ v1_partfun1('#skF_5',k2_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2216])).

tff(c_2310,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_3'),k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2300,c_149])).

tff(c_2308,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'),k2_relat_1('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2300,c_2097])).

tff(c_2509,plain,(
    ! [C_461,A_462,B_463] :
      ( v1_partfun1(C_461,A_462)
      | ~ v1_funct_2(C_461,A_462,B_463)
      | ~ v1_funct_1(C_461)
      | ~ m1_subset_1(C_461,k1_zfmisc_1(k2_zfmisc_1(A_462,B_463)))
      | v1_xboole_0(B_463) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2512,plain,
    ( v1_partfun1('#skF_5',k2_struct_0('#skF_3'))
    | ~ v1_funct_2('#skF_5',k2_struct_0('#skF_3'),k2_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0(k2_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_2308,c_2509])).

tff(c_2521,plain,
    ( v1_partfun1('#skF_5',k2_struct_0('#skF_3'))
    | v1_xboole_0(k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_2310,c_2512])).

tff(c_2523,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2309,c_2250,c_2521])).

tff(c_2524,plain,(
    k2_struct_0('#skF_3') = k1_relat_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_2216])).

tff(c_2528,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),k2_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2524,c_2097])).

tff(c_2690,plain,(
    ! [A_482,B_483,C_484] :
      ( k2_relset_1(A_482,B_483,C_484) = k2_relat_1(C_484)
      | ~ m1_subset_1(C_484,k1_zfmisc_1(k2_zfmisc_1(A_482,B_483))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2700,plain,(
    k2_relset_1(k1_relat_1('#skF_5'),k2_struct_0('#skF_4'),'#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2528,c_2690])).

tff(c_2530,plain,(
    k2_relset_1(k1_relat_1('#skF_5'),k2_struct_0('#skF_4'),'#skF_5') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2524,c_150])).

tff(c_2701,plain,(
    k2_struct_0('#skF_4') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2700,c_2530])).

tff(c_2711,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2701,c_166])).

tff(c_2720,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_20,c_2711])).

tff(c_121,plain,(
    ! [A_55] :
      ( v1_xboole_0(A_55)
      | r2_hidden('#skF_1'(A_55),A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_10] : k2_zfmisc_1(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_112,plain,(
    ! [A_50,B_51] : ~ r2_hidden(A_50,k2_zfmisc_1(A_50,B_51)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_118,plain,(
    ! [A_10] : ~ r2_hidden(A_10,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_112])).

tff(c_130,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_121,c_118])).

tff(c_16,plain,(
    ! [B_11] : k2_zfmisc_1(k1_xboole_0,B_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2531,plain,(
    v1_funct_2('#skF_5',k1_relat_1('#skF_5'),k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2524,c_149])).

tff(c_2709,plain,(
    v1_funct_2('#skF_5',k1_relat_1('#skF_5'),k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2701,c_2531])).

tff(c_2706,plain,(
    k2_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2701,c_2700])).

tff(c_2708,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2701,c_2528])).

tff(c_3010,plain,(
    ! [A_548,B_549,C_550] :
      ( k2_tops_2(A_548,B_549,C_550) = k2_funct_1(C_550)
      | ~ v2_funct_1(C_550)
      | k2_relset_1(A_548,B_549,C_550) != B_549
      | ~ m1_subset_1(C_550,k1_zfmisc_1(k2_zfmisc_1(A_548,B_549)))
      | ~ v1_funct_2(C_550,A_548,B_549)
      | ~ v1_funct_1(C_550) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_3016,plain,
    ( k2_tops_2(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5') = k2_funct_1('#skF_5')
    | ~ v2_funct_1('#skF_5')
    | k2_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5') != k2_relat_1('#skF_5')
    | ~ v1_funct_2('#skF_5',k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2708,c_3010])).

tff(c_3026,plain,(
    k2_tops_2(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5') = k2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_2709,c_2706,c_70,c_3016])).

tff(c_68,plain,
    ( k2_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')) != k2_struct_0('#skF_3')
    | k1_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')) != k2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_2117,plain,
    ( k2_relset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_3'),k2_tops_2(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'),'#skF_5')) != k2_struct_0('#skF_3')
    | k1_relset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_3'),k2_tops_2(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'),'#skF_5')) != k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_138,c_139,c_139,c_138,c_138,c_139,c_139,c_68])).

tff(c_2118,plain,(
    k1_relset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_3'),k2_tops_2(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'),'#skF_5')) != k2_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2117])).

tff(c_2527,plain,(
    k1_relset_1(k2_struct_0('#skF_4'),k1_relat_1('#skF_5'),k2_tops_2(k1_relat_1('#skF_5'),k2_struct_0('#skF_4'),'#skF_5')) != k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2524,c_2524,c_2118])).

tff(c_2707,plain,(
    k1_relset_1(k2_relat_1('#skF_5'),k1_relat_1('#skF_5'),k2_tops_2(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5')) != k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2701,c_2701,c_2701,c_2527])).

tff(c_3030,plain,(
    k1_relset_1(k2_relat_1('#skF_5'),k1_relat_1('#skF_5'),k2_funct_1('#skF_5')) != k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3026,c_2707])).

tff(c_2912,plain,(
    ! [A_531,B_532,C_533] :
      ( v1_funct_2(k2_tops_2(A_531,B_532,C_533),B_532,A_531)
      | ~ m1_subset_1(C_533,k1_zfmisc_1(k2_zfmisc_1(A_531,B_532)))
      | ~ v1_funct_2(C_533,A_531,B_532)
      | ~ v1_funct_1(C_533) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_2914,plain,
    ( v1_funct_2(k2_tops_2(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5'),k2_relat_1('#skF_5'),k1_relat_1('#skF_5'))
    | ~ v1_funct_2('#skF_5',k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2708,c_2912])).

tff(c_2921,plain,(
    v1_funct_2(k2_tops_2(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5'),k2_relat_1('#skF_5'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_2709,c_2914])).

tff(c_3028,plain,(
    v1_funct_2(k2_funct_1('#skF_5'),k2_relat_1('#skF_5'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3026,c_2921])).

tff(c_3034,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_5'),k1_relat_1('#skF_5'))))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))))
    | ~ v1_funct_2('#skF_5',k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3026,c_62])).

tff(c_3038,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_5'),k1_relat_1('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_2709,c_2708,c_3034])).

tff(c_50,plain,(
    ! [B_31,A_30,C_32] :
      ( k1_xboole_0 = B_31
      | k1_relset_1(A_30,B_31,C_32) = A_30
      | ~ v1_funct_2(C_32,A_30,B_31)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_3056,plain,
    ( k1_relat_1('#skF_5') = k1_xboole_0
    | k1_relset_1(k2_relat_1('#skF_5'),k1_relat_1('#skF_5'),k2_funct_1('#skF_5')) = k2_relat_1('#skF_5')
    | ~ v1_funct_2(k2_funct_1('#skF_5'),k2_relat_1('#skF_5'),k1_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_3038,c_50])).

tff(c_3088,plain,
    ( k1_relat_1('#skF_5') = k1_xboole_0
    | k1_relset_1(k2_relat_1('#skF_5'),k1_relat_1('#skF_5'),k2_funct_1('#skF_5')) = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3028,c_3056])).

tff(c_3089,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_3030,c_3088])).

tff(c_22,plain,(
    ! [A_15] :
      ( r1_tarski(A_15,k2_zfmisc_1(k1_relat_1(A_15),k2_relat_1(A_15)))
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2153,plain,(
    ! [C_395,B_396,A_397] :
      ( r2_hidden(C_395,B_396)
      | ~ r2_hidden(C_395,A_397)
      | ~ r1_tarski(A_397,B_396) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2174,plain,(
    ! [A_405,B_406] :
      ( r2_hidden('#skF_1'(A_405),B_406)
      | ~ r1_tarski(A_405,B_406)
      | v1_xboole_0(A_405) ) ),
    inference(resolution,[status(thm)],[c_4,c_2153])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2217,plain,(
    ! [B_410,A_411] :
      ( ~ v1_xboole_0(B_410)
      | ~ r1_tarski(A_411,B_410)
      | v1_xboole_0(A_411) ) ),
    inference(resolution,[status(thm)],[c_2174,c_2])).

tff(c_2230,plain,(
    ! [A_15] :
      ( ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1(A_15),k2_relat_1(A_15)))
      | v1_xboole_0(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(resolution,[status(thm)],[c_22,c_2217])).

tff(c_3132,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k2_relat_1('#skF_5')))
    | v1_xboole_0('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3089,c_2230])).

tff(c_3156,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2138,c_130,c_16,c_3132])).

tff(c_3158,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2720,c_3156])).

tff(c_3159,plain,(
    k2_relset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_3'),k2_tops_2(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'),'#skF_5')) != k2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_2117])).

tff(c_3560,plain,(
    k2_relset_1(k2_struct_0('#skF_4'),k1_relat_1('#skF_5'),k2_tops_2(k1_relat_1('#skF_5'),k2_struct_0('#skF_4'),'#skF_5')) != k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3558,c_3558,c_3558,c_3159])).

tff(c_3809,plain,(
    k2_relset_1(k2_relat_1('#skF_5'),k1_relat_1('#skF_5'),k2_tops_2(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5')) != k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3737,c_3737,c_3560])).

tff(c_4062,plain,(
    k2_relset_1(k2_relat_1('#skF_5'),k1_relat_1('#skF_5'),k2_funct_1('#skF_5')) != k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4057,c_3809])).

tff(c_4172,plain,(
    k2_relat_1(k2_funct_1('#skF_5')) != k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4129,c_4062])).

tff(c_4179,plain,
    ( ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_4172])).

tff(c_4183,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3180,c_78,c_70,c_4179])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:48:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.76/2.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.76/2.14  
% 5.76/2.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.76/2.15  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 5.76/2.15  
% 5.76/2.15  %Foreground sorts:
% 5.76/2.15  
% 5.76/2.15  
% 5.76/2.15  %Background operators:
% 5.76/2.15  
% 5.76/2.15  
% 5.76/2.15  %Foreground operators:
% 5.76/2.15  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.76/2.15  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.76/2.15  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.76/2.15  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.76/2.15  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.76/2.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.76/2.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.76/2.15  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.76/2.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.76/2.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.76/2.15  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.76/2.15  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 5.76/2.15  tff('#skF_5', type, '#skF_5': $i).
% 5.76/2.15  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.76/2.15  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.76/2.15  tff('#skF_3', type, '#skF_3': $i).
% 5.76/2.15  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.76/2.15  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.76/2.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.76/2.15  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.76/2.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.76/2.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.76/2.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.76/2.15  tff('#skF_4', type, '#skF_4': $i).
% 5.76/2.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.76/2.15  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.76/2.15  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.76/2.15  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.76/2.15  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 5.76/2.15  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.76/2.15  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.76/2.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.76/2.15  
% 5.76/2.17  tff(f_179, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_2)).
% 5.76/2.17  tff(f_123, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 5.76/2.17  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.76/2.17  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 5.76/2.17  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.76/2.17  tff(f_131, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 5.76/2.17  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.76/2.17  tff(f_119, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 5.76/2.17  tff(f_93, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 5.76/2.17  tff(f_143, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 5.76/2.17  tff(f_155, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v1_funct_1(k2_tops_2(A, B, C)) & v1_funct_2(k2_tops_2(A, B, C), B, A)) & m1_subset_1(k2_tops_2(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_2)).
% 5.76/2.17  tff(f_51, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc11_relat_1)).
% 5.76/2.17  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.76/2.17  tff(f_44, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.76/2.17  tff(f_47, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 5.76/2.17  tff(f_111, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 5.76/2.17  tff(f_55, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 5.76/2.17  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.76/2.17  tff(c_80, plain, (l1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_179])).
% 5.76/2.17  tff(c_131, plain, (![A_56]: (u1_struct_0(A_56)=k2_struct_0(A_56) | ~l1_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.76/2.17  tff(c_138, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_80, c_131])).
% 5.76/2.17  tff(c_84, plain, (l1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_179])).
% 5.76/2.17  tff(c_139, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_84, c_131])).
% 5.76/2.17  tff(c_74, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_179])).
% 5.76/2.17  tff(c_2097, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_139, c_74])).
% 5.76/2.17  tff(c_3172, plain, (![C_553, A_554, B_555]: (v1_relat_1(C_553) | ~m1_subset_1(C_553, k1_zfmisc_1(k2_zfmisc_1(A_554, B_555))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.76/2.17  tff(c_3180, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_2097, c_3172])).
% 5.76/2.17  tff(c_78, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_179])).
% 5.76/2.17  tff(c_70, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_179])).
% 5.76/2.17  tff(c_24, plain, (![A_16]: (k2_relat_1(k2_funct_1(A_16))=k1_relat_1(A_16) | ~v2_funct_1(A_16) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.76/2.17  tff(c_3373, plain, (![A_590, B_591, C_592]: (k2_relset_1(A_590, B_591, C_592)=k2_relat_1(C_592) | ~m1_subset_1(C_592, k1_zfmisc_1(k2_zfmisc_1(A_590, B_591))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.76/2.17  tff(c_3383, plain, (k2_relset_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'), '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_2097, c_3373])).
% 5.76/2.17  tff(c_72, plain, (k2_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5')=k2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_179])).
% 5.76/2.17  tff(c_150, plain, (k2_relset_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'), '#skF_5')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_138, c_72])).
% 5.76/2.17  tff(c_3398, plain, (k2_struct_0('#skF_4')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3383, c_150])).
% 5.76/2.17  tff(c_82, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_179])).
% 5.76/2.17  tff(c_155, plain, (![A_57]: (~v1_xboole_0(u1_struct_0(A_57)) | ~l1_struct_0(A_57) | v2_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.76/2.17  tff(c_161, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_138, c_155])).
% 5.76/2.17  tff(c_165, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_161])).
% 5.76/2.17  tff(c_166, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_82, c_165])).
% 5.76/2.17  tff(c_3408, plain, (~v1_xboole_0(k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_3398, c_166])).
% 5.76/2.17  tff(c_3206, plain, (![C_566, A_567, B_568]: (v4_relat_1(C_566, A_567) | ~m1_subset_1(C_566, k1_zfmisc_1(k2_zfmisc_1(A_567, B_568))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.76/2.17  tff(c_3216, plain, (v4_relat_1('#skF_5', k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_2097, c_3206])).
% 5.76/2.17  tff(c_3291, plain, (![B_581, A_582]: (k1_relat_1(B_581)=A_582 | ~v1_partfun1(B_581, A_582) | ~v4_relat_1(B_581, A_582) | ~v1_relat_1(B_581))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.76/2.17  tff(c_3294, plain, (k2_struct_0('#skF_3')=k1_relat_1('#skF_5') | ~v1_partfun1('#skF_5', k2_struct_0('#skF_3')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_3216, c_3291])).
% 5.76/2.17  tff(c_3297, plain, (k2_struct_0('#skF_3')=k1_relat_1('#skF_5') | ~v1_partfun1('#skF_5', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3180, c_3294])).
% 5.76/2.17  tff(c_3298, plain, (~v1_partfun1('#skF_5', k2_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_3297])).
% 5.76/2.17  tff(c_76, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_179])).
% 5.76/2.17  tff(c_140, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_3'), k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_76])).
% 5.76/2.17  tff(c_149, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_3'), k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_140])).
% 5.76/2.17  tff(c_3409, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_3'), k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_3398, c_149])).
% 5.76/2.17  tff(c_3407, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'), k2_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_3398, c_2097])).
% 5.76/2.17  tff(c_3543, plain, (![C_630, A_631, B_632]: (v1_partfun1(C_630, A_631) | ~v1_funct_2(C_630, A_631, B_632) | ~v1_funct_1(C_630) | ~m1_subset_1(C_630, k1_zfmisc_1(k2_zfmisc_1(A_631, B_632))) | v1_xboole_0(B_632))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.76/2.17  tff(c_3546, plain, (v1_partfun1('#skF_5', k2_struct_0('#skF_3')) | ~v1_funct_2('#skF_5', k2_struct_0('#skF_3'), k2_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | v1_xboole_0(k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_3407, c_3543])).
% 5.76/2.17  tff(c_3555, plain, (v1_partfun1('#skF_5', k2_struct_0('#skF_3')) | v1_xboole_0(k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_3409, c_3546])).
% 5.76/2.17  tff(c_3557, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3408, c_3298, c_3555])).
% 5.76/2.17  tff(c_3558, plain, (k2_struct_0('#skF_3')=k1_relat_1('#skF_5')), inference(splitRight, [status(thm)], [c_3297])).
% 5.76/2.17  tff(c_3563, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_3558, c_2097])).
% 5.76/2.17  tff(c_3726, plain, (![A_648, B_649, C_650]: (k2_relset_1(A_648, B_649, C_650)=k2_relat_1(C_650) | ~m1_subset_1(C_650, k1_zfmisc_1(k2_zfmisc_1(A_648, B_649))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.76/2.17  tff(c_3736, plain, (k2_relset_1(k1_relat_1('#skF_5'), k2_struct_0('#skF_4'), '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_3563, c_3726])).
% 5.76/2.17  tff(c_3565, plain, (k2_relset_1(k1_relat_1('#skF_5'), k2_struct_0('#skF_4'), '#skF_5')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3558, c_150])).
% 5.76/2.17  tff(c_3737, plain, (k2_struct_0('#skF_4')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3736, c_3565])).
% 5.76/2.17  tff(c_3566, plain, (v1_funct_2('#skF_5', k1_relat_1('#skF_5'), k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3558, c_149])).
% 5.76/2.17  tff(c_3745, plain, (v1_funct_2('#skF_5', k1_relat_1('#skF_5'), k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_3737, c_3566])).
% 5.76/2.17  tff(c_3744, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_3737, c_3563])).
% 5.76/2.17  tff(c_3742, plain, (k2_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3737, c_3736])).
% 5.76/2.17  tff(c_4041, plain, (![A_710, B_711, C_712]: (k2_tops_2(A_710, B_711, C_712)=k2_funct_1(C_712) | ~v2_funct_1(C_712) | k2_relset_1(A_710, B_711, C_712)!=B_711 | ~m1_subset_1(C_712, k1_zfmisc_1(k2_zfmisc_1(A_710, B_711))) | ~v1_funct_2(C_712, A_710, B_711) | ~v1_funct_1(C_712))), inference(cnfTransformation, [status(thm)], [f_143])).
% 5.76/2.17  tff(c_4047, plain, (k2_tops_2(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5')=k2_funct_1('#skF_5') | ~v2_funct_1('#skF_5') | k2_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5')!=k2_relat_1('#skF_5') | ~v1_funct_2('#skF_5', k1_relat_1('#skF_5'), k2_relat_1('#skF_5')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_3744, c_4041])).
% 5.76/2.17  tff(c_4057, plain, (k2_tops_2(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5')=k2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_3745, c_3742, c_70, c_4047])).
% 5.76/2.17  tff(c_62, plain, (![A_40, B_41, C_42]: (m1_subset_1(k2_tops_2(A_40, B_41, C_42), k1_zfmisc_1(k2_zfmisc_1(B_41, A_40))) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))) | ~v1_funct_2(C_42, A_40, B_41) | ~v1_funct_1(C_42))), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.76/2.17  tff(c_4066, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_5'), k1_relat_1('#skF_5')))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5')))) | ~v1_funct_2('#skF_5', k1_relat_1('#skF_5'), k2_relat_1('#skF_5')) | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_4057, c_62])).
% 5.76/2.17  tff(c_4070, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_5'), k1_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_3745, c_3744, c_4066])).
% 5.76/2.17  tff(c_34, plain, (![A_23, B_24, C_25]: (k2_relset_1(A_23, B_24, C_25)=k2_relat_1(C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.76/2.17  tff(c_4129, plain, (k2_relset_1(k2_relat_1('#skF_5'), k1_relat_1('#skF_5'), k2_funct_1('#skF_5'))=k2_relat_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_4070, c_34])).
% 5.76/2.17  tff(c_20, plain, (![A_14]: (v1_xboole_0(k2_relat_1(A_14)) | ~v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.76/2.17  tff(c_2289, plain, (![A_417, B_418, C_419]: (k2_relset_1(A_417, B_418, C_419)=k2_relat_1(C_419) | ~m1_subset_1(C_419, k1_zfmisc_1(k2_zfmisc_1(A_417, B_418))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.76/2.17  tff(c_2299, plain, (k2_relset_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'), '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_2097, c_2289])).
% 5.76/2.17  tff(c_2300, plain, (k2_struct_0('#skF_4')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2299, c_150])).
% 5.76/2.17  tff(c_2309, plain, (~v1_xboole_0(k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2300, c_166])).
% 5.76/2.17  tff(c_2130, plain, (![C_385, A_386, B_387]: (v1_relat_1(C_385) | ~m1_subset_1(C_385, k1_zfmisc_1(k2_zfmisc_1(A_386, B_387))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.76/2.17  tff(c_2138, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_2097, c_2130])).
% 5.76/2.17  tff(c_2160, plain, (![C_398, A_399, B_400]: (v4_relat_1(C_398, A_399) | ~m1_subset_1(C_398, k1_zfmisc_1(k2_zfmisc_1(A_399, B_400))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.76/2.17  tff(c_2170, plain, (v4_relat_1('#skF_5', k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_2097, c_2160])).
% 5.76/2.17  tff(c_2210, plain, (![B_408, A_409]: (k1_relat_1(B_408)=A_409 | ~v1_partfun1(B_408, A_409) | ~v4_relat_1(B_408, A_409) | ~v1_relat_1(B_408))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.76/2.17  tff(c_2213, plain, (k2_struct_0('#skF_3')=k1_relat_1('#skF_5') | ~v1_partfun1('#skF_5', k2_struct_0('#skF_3')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_2170, c_2210])).
% 5.76/2.17  tff(c_2216, plain, (k2_struct_0('#skF_3')=k1_relat_1('#skF_5') | ~v1_partfun1('#skF_5', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2138, c_2213])).
% 5.76/2.17  tff(c_2250, plain, (~v1_partfun1('#skF_5', k2_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_2216])).
% 5.76/2.17  tff(c_2310, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_3'), k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2300, c_149])).
% 5.76/2.17  tff(c_2308, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'), k2_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_2300, c_2097])).
% 5.76/2.17  tff(c_2509, plain, (![C_461, A_462, B_463]: (v1_partfun1(C_461, A_462) | ~v1_funct_2(C_461, A_462, B_463) | ~v1_funct_1(C_461) | ~m1_subset_1(C_461, k1_zfmisc_1(k2_zfmisc_1(A_462, B_463))) | v1_xboole_0(B_463))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.76/2.17  tff(c_2512, plain, (v1_partfun1('#skF_5', k2_struct_0('#skF_3')) | ~v1_funct_2('#skF_5', k2_struct_0('#skF_3'), k2_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | v1_xboole_0(k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_2308, c_2509])).
% 5.76/2.17  tff(c_2521, plain, (v1_partfun1('#skF_5', k2_struct_0('#skF_3')) | v1_xboole_0(k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_2310, c_2512])).
% 5.76/2.17  tff(c_2523, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2309, c_2250, c_2521])).
% 5.76/2.17  tff(c_2524, plain, (k2_struct_0('#skF_3')=k1_relat_1('#skF_5')), inference(splitRight, [status(thm)], [c_2216])).
% 5.76/2.17  tff(c_2528, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_2524, c_2097])).
% 5.76/2.17  tff(c_2690, plain, (![A_482, B_483, C_484]: (k2_relset_1(A_482, B_483, C_484)=k2_relat_1(C_484) | ~m1_subset_1(C_484, k1_zfmisc_1(k2_zfmisc_1(A_482, B_483))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.76/2.17  tff(c_2700, plain, (k2_relset_1(k1_relat_1('#skF_5'), k2_struct_0('#skF_4'), '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_2528, c_2690])).
% 5.76/2.17  tff(c_2530, plain, (k2_relset_1(k1_relat_1('#skF_5'), k2_struct_0('#skF_4'), '#skF_5')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2524, c_150])).
% 5.76/2.17  tff(c_2701, plain, (k2_struct_0('#skF_4')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2700, c_2530])).
% 5.76/2.17  tff(c_2711, plain, (~v1_xboole_0(k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2701, c_166])).
% 5.76/2.17  tff(c_2720, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_20, c_2711])).
% 5.76/2.17  tff(c_121, plain, (![A_55]: (v1_xboole_0(A_55) | r2_hidden('#skF_1'(A_55), A_55))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.76/2.17  tff(c_14, plain, (![A_10]: (k2_zfmisc_1(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.76/2.17  tff(c_112, plain, (![A_50, B_51]: (~r2_hidden(A_50, k2_zfmisc_1(A_50, B_51)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.76/2.17  tff(c_118, plain, (![A_10]: (~r2_hidden(A_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_112])).
% 5.76/2.17  tff(c_130, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_121, c_118])).
% 5.76/2.17  tff(c_16, plain, (![B_11]: (k2_zfmisc_1(k1_xboole_0, B_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.76/2.17  tff(c_2531, plain, (v1_funct_2('#skF_5', k1_relat_1('#skF_5'), k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2524, c_149])).
% 5.76/2.17  tff(c_2709, plain, (v1_funct_2('#skF_5', k1_relat_1('#skF_5'), k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2701, c_2531])).
% 5.76/2.17  tff(c_2706, plain, (k2_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2701, c_2700])).
% 5.76/2.17  tff(c_2708, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_2701, c_2528])).
% 5.76/2.17  tff(c_3010, plain, (![A_548, B_549, C_550]: (k2_tops_2(A_548, B_549, C_550)=k2_funct_1(C_550) | ~v2_funct_1(C_550) | k2_relset_1(A_548, B_549, C_550)!=B_549 | ~m1_subset_1(C_550, k1_zfmisc_1(k2_zfmisc_1(A_548, B_549))) | ~v1_funct_2(C_550, A_548, B_549) | ~v1_funct_1(C_550))), inference(cnfTransformation, [status(thm)], [f_143])).
% 5.76/2.17  tff(c_3016, plain, (k2_tops_2(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5')=k2_funct_1('#skF_5') | ~v2_funct_1('#skF_5') | k2_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5')!=k2_relat_1('#skF_5') | ~v1_funct_2('#skF_5', k1_relat_1('#skF_5'), k2_relat_1('#skF_5')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_2708, c_3010])).
% 5.76/2.17  tff(c_3026, plain, (k2_tops_2(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5')=k2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_2709, c_2706, c_70, c_3016])).
% 5.76/2.17  tff(c_68, plain, (k2_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'))!=k2_struct_0('#skF_3') | k1_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'))!=k2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_179])).
% 5.76/2.17  tff(c_2117, plain, (k2_relset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_3'), k2_tops_2(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'), '#skF_5'))!=k2_struct_0('#skF_3') | k1_relset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_3'), k2_tops_2(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'), '#skF_5'))!=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_138, c_138, c_139, c_139, c_138, c_138, c_139, c_139, c_68])).
% 5.76/2.17  tff(c_2118, plain, (k1_relset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_3'), k2_tops_2(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'), '#skF_5'))!=k2_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_2117])).
% 5.76/2.17  tff(c_2527, plain, (k1_relset_1(k2_struct_0('#skF_4'), k1_relat_1('#skF_5'), k2_tops_2(k1_relat_1('#skF_5'), k2_struct_0('#skF_4'), '#skF_5'))!=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2524, c_2524, c_2118])).
% 5.76/2.17  tff(c_2707, plain, (k1_relset_1(k2_relat_1('#skF_5'), k1_relat_1('#skF_5'), k2_tops_2(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5'))!=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2701, c_2701, c_2701, c_2527])).
% 5.76/2.17  tff(c_3030, plain, (k1_relset_1(k2_relat_1('#skF_5'), k1_relat_1('#skF_5'), k2_funct_1('#skF_5'))!=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3026, c_2707])).
% 5.76/2.17  tff(c_2912, plain, (![A_531, B_532, C_533]: (v1_funct_2(k2_tops_2(A_531, B_532, C_533), B_532, A_531) | ~m1_subset_1(C_533, k1_zfmisc_1(k2_zfmisc_1(A_531, B_532))) | ~v1_funct_2(C_533, A_531, B_532) | ~v1_funct_1(C_533))), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.76/2.17  tff(c_2914, plain, (v1_funct_2(k2_tops_2(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5'), k2_relat_1('#skF_5'), k1_relat_1('#skF_5')) | ~v1_funct_2('#skF_5', k1_relat_1('#skF_5'), k2_relat_1('#skF_5')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_2708, c_2912])).
% 5.76/2.17  tff(c_2921, plain, (v1_funct_2(k2_tops_2(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5'), k2_relat_1('#skF_5'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_2709, c_2914])).
% 5.76/2.17  tff(c_3028, plain, (v1_funct_2(k2_funct_1('#skF_5'), k2_relat_1('#skF_5'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_3026, c_2921])).
% 5.76/2.17  tff(c_3034, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_5'), k1_relat_1('#skF_5')))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5')))) | ~v1_funct_2('#skF_5', k1_relat_1('#skF_5'), k2_relat_1('#skF_5')) | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3026, c_62])).
% 5.76/2.17  tff(c_3038, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_5'), k1_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_2709, c_2708, c_3034])).
% 5.76/2.17  tff(c_50, plain, (![B_31, A_30, C_32]: (k1_xboole_0=B_31 | k1_relset_1(A_30, B_31, C_32)=A_30 | ~v1_funct_2(C_32, A_30, B_31) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.76/2.17  tff(c_3056, plain, (k1_relat_1('#skF_5')=k1_xboole_0 | k1_relset_1(k2_relat_1('#skF_5'), k1_relat_1('#skF_5'), k2_funct_1('#skF_5'))=k2_relat_1('#skF_5') | ~v1_funct_2(k2_funct_1('#skF_5'), k2_relat_1('#skF_5'), k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_3038, c_50])).
% 5.76/2.17  tff(c_3088, plain, (k1_relat_1('#skF_5')=k1_xboole_0 | k1_relset_1(k2_relat_1('#skF_5'), k1_relat_1('#skF_5'), k2_funct_1('#skF_5'))=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3028, c_3056])).
% 5.76/2.17  tff(c_3089, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_3030, c_3088])).
% 5.76/2.17  tff(c_22, plain, (![A_15]: (r1_tarski(A_15, k2_zfmisc_1(k1_relat_1(A_15), k2_relat_1(A_15))) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.76/2.17  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.76/2.17  tff(c_2153, plain, (![C_395, B_396, A_397]: (r2_hidden(C_395, B_396) | ~r2_hidden(C_395, A_397) | ~r1_tarski(A_397, B_396))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.76/2.17  tff(c_2174, plain, (![A_405, B_406]: (r2_hidden('#skF_1'(A_405), B_406) | ~r1_tarski(A_405, B_406) | v1_xboole_0(A_405))), inference(resolution, [status(thm)], [c_4, c_2153])).
% 5.76/2.17  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.76/2.17  tff(c_2217, plain, (![B_410, A_411]: (~v1_xboole_0(B_410) | ~r1_tarski(A_411, B_410) | v1_xboole_0(A_411))), inference(resolution, [status(thm)], [c_2174, c_2])).
% 5.76/2.17  tff(c_2230, plain, (![A_15]: (~v1_xboole_0(k2_zfmisc_1(k1_relat_1(A_15), k2_relat_1(A_15))) | v1_xboole_0(A_15) | ~v1_relat_1(A_15))), inference(resolution, [status(thm)], [c_22, c_2217])).
% 5.76/2.17  tff(c_3132, plain, (~v1_xboole_0(k2_zfmisc_1(k1_xboole_0, k2_relat_1('#skF_5'))) | v1_xboole_0('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3089, c_2230])).
% 5.76/2.17  tff(c_3156, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2138, c_130, c_16, c_3132])).
% 5.76/2.17  tff(c_3158, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2720, c_3156])).
% 5.76/2.17  tff(c_3159, plain, (k2_relset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_3'), k2_tops_2(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'), '#skF_5'))!=k2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_2117])).
% 5.76/2.17  tff(c_3560, plain, (k2_relset_1(k2_struct_0('#skF_4'), k1_relat_1('#skF_5'), k2_tops_2(k1_relat_1('#skF_5'), k2_struct_0('#skF_4'), '#skF_5'))!=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3558, c_3558, c_3558, c_3159])).
% 5.76/2.17  tff(c_3809, plain, (k2_relset_1(k2_relat_1('#skF_5'), k1_relat_1('#skF_5'), k2_tops_2(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5'))!=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3737, c_3737, c_3560])).
% 5.76/2.17  tff(c_4062, plain, (k2_relset_1(k2_relat_1('#skF_5'), k1_relat_1('#skF_5'), k2_funct_1('#skF_5'))!=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4057, c_3809])).
% 5.76/2.17  tff(c_4172, plain, (k2_relat_1(k2_funct_1('#skF_5'))!=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4129, c_4062])).
% 5.76/2.17  tff(c_4179, plain, (~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_24, c_4172])).
% 5.76/2.17  tff(c_4183, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3180, c_78, c_70, c_4179])).
% 5.76/2.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.76/2.17  
% 5.76/2.17  Inference rules
% 5.76/2.17  ----------------------
% 5.76/2.17  #Ref     : 0
% 5.76/2.17  #Sup     : 980
% 5.76/2.17  #Fact    : 0
% 5.76/2.17  #Define  : 0
% 5.76/2.17  #Split   : 17
% 5.76/2.17  #Chain   : 0
% 5.76/2.17  #Close   : 0
% 5.76/2.17  
% 5.76/2.17  Ordering : KBO
% 5.76/2.17  
% 5.76/2.17  Simplification rules
% 5.76/2.17  ----------------------
% 5.76/2.17  #Subsume      : 138
% 5.76/2.17  #Demod        : 531
% 5.76/2.17  #Tautology    : 345
% 5.76/2.17  #SimpNegUnit  : 24
% 5.76/2.17  #BackRed      : 142
% 5.76/2.17  
% 5.76/2.17  #Partial instantiations: 0
% 5.76/2.17  #Strategies tried      : 1
% 5.76/2.17  
% 5.76/2.17  Timing (in seconds)
% 5.76/2.17  ----------------------
% 5.76/2.18  Preprocessing        : 0.36
% 5.76/2.18  Parsing              : 0.19
% 5.76/2.18  CNF conversion       : 0.03
% 5.76/2.18  Main loop            : 0.98
% 5.76/2.18  Inferencing          : 0.36
% 5.76/2.18  Reduction            : 0.31
% 5.76/2.18  Demodulation         : 0.22
% 5.76/2.18  BG Simplification    : 0.04
% 5.76/2.18  Subsumption          : 0.18
% 5.76/2.18  Abstraction          : 0.04
% 5.76/2.18  MUC search           : 0.00
% 5.76/2.18  Cooper               : 0.00
% 5.76/2.18  Total                : 1.40
% 5.76/2.18  Index Insertion      : 0.00
% 5.76/2.18  Index Deletion       : 0.00
% 5.76/2.18  Index Matching       : 0.00
% 5.76/2.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
