%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1188+1.001 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 4.13s
% Output     : CNFRefutation 4.67s
% Verified   : 
% Statistics : Number of formulae       :  183 (1702 expanded)
%              Number of leaves         :   47 ( 623 expanded)
%              Depth                    :   27
%              Number of atoms          :  549 (7608 expanded)
%              Number of equality atoms :   59 ( 743 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r1_orders_2 > v1_partfun1 > r8_orders_1 > r2_hidden > m1_subset_1 > v8_relat_2 > v5_orders_2 > v4_relat_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_orders_2 > v1_xboole_0 > v1_relat_2 > v1_relat_1 > l1_struct_0 > l1_orders_2 > k4_tarski > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k3_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r8_orders_1,type,(
    r8_orders_1: ( $i * $i ) > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(v1_relat_2,type,(
    v1_relat_2: $i > $o )).

tff(v8_relat_2,type,(
    v8_relat_2: $i > $o )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(v4_relat_2,type,(
    v4_relat_2: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v2_orders_2,type,(
    v2_orders_2: $i > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

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

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_166,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( r8_orders_1(u1_orders_2(A),B)
            <=> ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ( B != C
                   => r2_orders_2(A,C,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_orders_2)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_141,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_30,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v3_orders_2(A)
       => v2_orders_2(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_orders_2)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_103,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & l1_orders_2(A) )
     => v1_relat_2(u1_orders_2(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_orders_2)).

tff(f_111,axiom,(
    ! [A] :
      ( ( v2_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => v4_relat_2(u1_orders_2(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_orders_2)).

tff(f_119,axiom,(
    ! [A] :
      ( ( v2_orders_2(A)
        & v4_orders_2(A)
        & l1_orders_2(A) )
     => v8_relat_2(u1_orders_2(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_orders_2)).

tff(f_89,axiom,(
    ! [A] :
      ( ( v2_orders_2(A)
        & l1_orders_2(A) )
     => v1_partfun1(u1_orders_2(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_orders_2)).

tff(f_131,axiom,(
    ! [A,B] :
      ( ( v1_relat_2(B)
        & v4_relat_2(B)
        & v8_relat_2(B)
        & v1_partfun1(B,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k3_relat_1(B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_orders_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r8_orders_1(A,B)
        <=> ( r2_hidden(B,k3_relat_1(A))
            & ! [C] :
                ( r2_hidden(C,k3_relat_1(A))
               => ( C = B
                  | r2_hidden(k4_tarski(C,B),A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_orders_1)).

tff(f_135,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_49,axiom,(
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

tff(f_75,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_orders_2(A,B,C)
              <=> r2_hidden(k4_tarski(B,C),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

tff(f_97,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_48,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_26,plain,(
    ! [A_29] :
      ( l1_struct_0(A_29)
      | ~ l1_orders_2(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_44,plain,(
    ! [A_40,B_41] :
      ( r2_hidden(A_40,B_41)
      | v1_xboole_0(B_41)
      | ~ m1_subset_1(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_60,plain,
    ( '#skF_3' != '#skF_4'
    | ~ r8_orders_1(u1_orders_2('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_82,plain,(
    ~ r8_orders_1(u1_orders_2('#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_54,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_75,plain,(
    ! [A_53] :
      ( v2_orders_2(A_53)
      | ~ v3_orders_2(A_53)
      | ~ l1_orders_2(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_78,plain,
    ( v2_orders_2('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_75])).

tff(c_81,plain,(
    v2_orders_2('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_78])).

tff(c_50,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_52,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_102,plain,(
    ! [A_70] :
      ( m1_subset_1(u1_orders_2(A_70),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_70),u1_struct_0(A_70))))
      | ~ l1_orders_2(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_4,plain,(
    ! [C_4,A_2,B_3] :
      ( v1_relat_1(C_4)
      | ~ m1_subset_1(C_4,k1_zfmisc_1(k2_zfmisc_1(A_2,B_3))) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_106,plain,(
    ! [A_70] :
      ( v1_relat_1(u1_orders_2(A_70))
      | ~ l1_orders_2(A_70) ) ),
    inference(resolution,[status(thm)],[c_102,c_4])).

tff(c_34,plain,(
    ! [A_33] :
      ( v1_relat_2(u1_orders_2(A_33))
      | ~ l1_orders_2(A_33)
      | ~ v3_orders_2(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_36,plain,(
    ! [A_34] :
      ( v4_relat_2(u1_orders_2(A_34))
      | ~ l1_orders_2(A_34)
      | ~ v5_orders_2(A_34)
      | ~ v2_orders_2(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_38,plain,(
    ! [A_35] :
      ( v8_relat_2(u1_orders_2(A_35))
      | ~ l1_orders_2(A_35)
      | ~ v4_orders_2(A_35)
      | ~ v2_orders_2(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_30,plain,(
    ! [A_31] :
      ( v1_partfun1(u1_orders_2(A_31),u1_struct_0(A_31))
      | ~ l1_orders_2(A_31)
      | ~ v2_orders_2(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_28,plain,(
    ! [A_30] :
      ( m1_subset_1(u1_orders_2(A_30),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_30),u1_struct_0(A_30))))
      | ~ l1_orders_2(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_202,plain,(
    ! [B_92,A_93] :
      ( k3_relat_1(B_92) = A_93
      | ~ m1_subset_1(B_92,k1_zfmisc_1(k2_zfmisc_1(A_93,A_93)))
      | ~ v1_partfun1(B_92,A_93)
      | ~ v8_relat_2(B_92)
      | ~ v4_relat_2(B_92)
      | ~ v1_relat_2(B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_294,plain,(
    ! [A_114] :
      ( k3_relat_1(u1_orders_2(A_114)) = u1_struct_0(A_114)
      | ~ v1_partfun1(u1_orders_2(A_114),u1_struct_0(A_114))
      | ~ v8_relat_2(u1_orders_2(A_114))
      | ~ v4_relat_2(u1_orders_2(A_114))
      | ~ v1_relat_2(u1_orders_2(A_114))
      | ~ l1_orders_2(A_114) ) ),
    inference(resolution,[status(thm)],[c_28,c_202])).

tff(c_299,plain,(
    ! [A_115] :
      ( k3_relat_1(u1_orders_2(A_115)) = u1_struct_0(A_115)
      | ~ v8_relat_2(u1_orders_2(A_115))
      | ~ v4_relat_2(u1_orders_2(A_115))
      | ~ v1_relat_2(u1_orders_2(A_115))
      | ~ l1_orders_2(A_115)
      | ~ v2_orders_2(A_115) ) ),
    inference(resolution,[status(thm)],[c_30,c_294])).

tff(c_304,plain,(
    ! [A_116] :
      ( k3_relat_1(u1_orders_2(A_116)) = u1_struct_0(A_116)
      | ~ v4_relat_2(u1_orders_2(A_116))
      | ~ v1_relat_2(u1_orders_2(A_116))
      | ~ l1_orders_2(A_116)
      | ~ v4_orders_2(A_116)
      | ~ v2_orders_2(A_116) ) ),
    inference(resolution,[status(thm)],[c_38,c_299])).

tff(c_309,plain,(
    ! [A_117] :
      ( k3_relat_1(u1_orders_2(A_117)) = u1_struct_0(A_117)
      | ~ v1_relat_2(u1_orders_2(A_117))
      | ~ v4_orders_2(A_117)
      | ~ l1_orders_2(A_117)
      | ~ v5_orders_2(A_117)
      | ~ v2_orders_2(A_117) ) ),
    inference(resolution,[status(thm)],[c_36,c_304])).

tff(c_314,plain,(
    ! [A_118] :
      ( k3_relat_1(u1_orders_2(A_118)) = u1_struct_0(A_118)
      | ~ v4_orders_2(A_118)
      | ~ v5_orders_2(A_118)
      | ~ v2_orders_2(A_118)
      | ~ l1_orders_2(A_118)
      | ~ v3_orders_2(A_118) ) ),
    inference(resolution,[status(thm)],[c_34,c_309])).

tff(c_18,plain,(
    ! [A_12,B_18] :
      ( '#skF_1'(A_12,B_18) != B_18
      | r8_orders_1(A_12,B_18)
      | ~ r2_hidden(B_18,k3_relat_1(A_12))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_415,plain,(
    ! [A_137,B_138] :
      ( '#skF_1'(u1_orders_2(A_137),B_138) != B_138
      | r8_orders_1(u1_orders_2(A_137),B_138)
      | ~ r2_hidden(B_138,u1_struct_0(A_137))
      | ~ v1_relat_1(u1_orders_2(A_137))
      | ~ v4_orders_2(A_137)
      | ~ v5_orders_2(A_137)
      | ~ v2_orders_2(A_137)
      | ~ l1_orders_2(A_137)
      | ~ v3_orders_2(A_137) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_18])).

tff(c_428,plain,
    ( '#skF_1'(u1_orders_2('#skF_2'),'#skF_3') != '#skF_3'
    | ~ r2_hidden('#skF_3',u1_struct_0('#skF_2'))
    | ~ v1_relat_1(u1_orders_2('#skF_2'))
    | ~ v4_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v2_orders_2('#skF_2')
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_415,c_82])).

tff(c_434,plain,
    ( '#skF_1'(u1_orders_2('#skF_2'),'#skF_3') != '#skF_3'
    | ~ r2_hidden('#skF_3',u1_struct_0('#skF_2'))
    | ~ v1_relat_1(u1_orders_2('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_81,c_50,c_52,c_428])).

tff(c_435,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_434])).

tff(c_457,plain,(
    ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_106,c_435])).

tff(c_461,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_457])).

tff(c_463,plain,(
    v1_relat_1(u1_orders_2('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_434])).

tff(c_313,plain,(
    ! [A_33] :
      ( k3_relat_1(u1_orders_2(A_33)) = u1_struct_0(A_33)
      | ~ v4_orders_2(A_33)
      | ~ v5_orders_2(A_33)
      | ~ v2_orders_2(A_33)
      | ~ l1_orders_2(A_33)
      | ~ v3_orders_2(A_33) ) ),
    inference(resolution,[status(thm)],[c_34,c_309])).

tff(c_462,plain,
    ( ~ r2_hidden('#skF_3',u1_struct_0('#skF_2'))
    | '#skF_1'(u1_orders_2('#skF_2'),'#skF_3') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_434])).

tff(c_464,plain,(
    '#skF_1'(u1_orders_2('#skF_2'),'#skF_3') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_462])).

tff(c_125,plain,(
    ! [A_75,B_76] :
      ( r2_hidden('#skF_1'(A_75,B_76),k3_relat_1(A_75))
      | r8_orders_1(A_75,B_76)
      | ~ r2_hidden(B_76,k3_relat_1(A_75))
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_42,plain,(
    ! [A_38,B_39] :
      ( m1_subset_1(A_38,B_39)
      | ~ r2_hidden(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_133,plain,(
    ! [A_75,B_76] :
      ( m1_subset_1('#skF_1'(A_75,B_76),k3_relat_1(A_75))
      | r8_orders_1(A_75,B_76)
      | ~ r2_hidden(B_76,k3_relat_1(A_75))
      | ~ v1_relat_1(A_75) ) ),
    inference(resolution,[status(thm)],[c_125,c_42])).

tff(c_325,plain,(
    ! [A_118,B_76] :
      ( m1_subset_1('#skF_1'(u1_orders_2(A_118),B_76),u1_struct_0(A_118))
      | r8_orders_1(u1_orders_2(A_118),B_76)
      | ~ r2_hidden(B_76,k3_relat_1(u1_orders_2(A_118)))
      | ~ v1_relat_1(u1_orders_2(A_118))
      | ~ v4_orders_2(A_118)
      | ~ v5_orders_2(A_118)
      | ~ v2_orders_2(A_118)
      | ~ l1_orders_2(A_118)
      | ~ v3_orders_2(A_118) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_133])).

tff(c_518,plain,(
    ! [A_154,B_155] :
      ( m1_subset_1('#skF_1'(u1_orders_2(A_154),B_155),u1_struct_0(A_154))
      | r8_orders_1(u1_orders_2(A_154),B_155)
      | ~ r2_hidden(B_155,k3_relat_1(u1_orders_2(A_154)))
      | ~ v1_relat_1(u1_orders_2(A_154))
      | ~ v4_orders_2(A_154)
      | ~ v5_orders_2(A_154)
      | ~ v2_orders_2(A_154)
      | ~ l1_orders_2(A_154)
      | ~ v3_orders_2(A_154) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_133])).

tff(c_72,plain,(
    ! [C_49] :
      ( r8_orders_1(u1_orders_2('#skF_2'),'#skF_3')
      | r2_orders_2('#skF_2',C_49,'#skF_3')
      | C_49 = '#skF_3'
      | ~ m1_subset_1(C_49,u1_struct_0('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_118,plain,(
    ! [C_49] :
      ( r2_orders_2('#skF_2',C_49,'#skF_3')
      | C_49 = '#skF_3'
      | ~ m1_subset_1(C_49,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_72])).

tff(c_524,plain,(
    ! [B_155] :
      ( r2_orders_2('#skF_2','#skF_1'(u1_orders_2('#skF_2'),B_155),'#skF_3')
      | '#skF_1'(u1_orders_2('#skF_2'),B_155) = '#skF_3'
      | r8_orders_1(u1_orders_2('#skF_2'),B_155)
      | ~ r2_hidden(B_155,k3_relat_1(u1_orders_2('#skF_2')))
      | ~ v1_relat_1(u1_orders_2('#skF_2'))
      | ~ v4_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v2_orders_2('#skF_2')
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_518,c_118])).

tff(c_530,plain,(
    ! [B_158] :
      ( r2_orders_2('#skF_2','#skF_1'(u1_orders_2('#skF_2'),B_158),'#skF_3')
      | '#skF_1'(u1_orders_2('#skF_2'),B_158) = '#skF_3'
      | r8_orders_1(u1_orders_2('#skF_2'),B_158)
      | ~ r2_hidden(B_158,k3_relat_1(u1_orders_2('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_81,c_50,c_52,c_463,c_524])).

tff(c_10,plain,(
    ! [A_5,B_9,C_11] :
      ( r1_orders_2(A_5,B_9,C_11)
      | ~ r2_orders_2(A_5,B_9,C_11)
      | ~ m1_subset_1(C_11,u1_struct_0(A_5))
      | ~ m1_subset_1(B_9,u1_struct_0(A_5))
      | ~ l1_orders_2(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_532,plain,(
    ! [B_158] :
      ( r1_orders_2('#skF_2','#skF_1'(u1_orders_2('#skF_2'),B_158),'#skF_3')
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(u1_orders_2('#skF_2'),B_158),u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | '#skF_1'(u1_orders_2('#skF_2'),B_158) = '#skF_3'
      | r8_orders_1(u1_orders_2('#skF_2'),B_158)
      | ~ r2_hidden(B_158,k3_relat_1(u1_orders_2('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_530,c_10])).

tff(c_536,plain,(
    ! [B_159] :
      ( r1_orders_2('#skF_2','#skF_1'(u1_orders_2('#skF_2'),B_159),'#skF_3')
      | ~ m1_subset_1('#skF_1'(u1_orders_2('#skF_2'),B_159),u1_struct_0('#skF_2'))
      | '#skF_1'(u1_orders_2('#skF_2'),B_159) = '#skF_3'
      | r8_orders_1(u1_orders_2('#skF_2'),B_159)
      | ~ r2_hidden(B_159,k3_relat_1(u1_orders_2('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_532])).

tff(c_540,plain,(
    ! [B_76] :
      ( r1_orders_2('#skF_2','#skF_1'(u1_orders_2('#skF_2'),B_76),'#skF_3')
      | '#skF_1'(u1_orders_2('#skF_2'),B_76) = '#skF_3'
      | r8_orders_1(u1_orders_2('#skF_2'),B_76)
      | ~ r2_hidden(B_76,k3_relat_1(u1_orders_2('#skF_2')))
      | ~ v1_relat_1(u1_orders_2('#skF_2'))
      | ~ v4_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v2_orders_2('#skF_2')
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_325,c_536])).

tff(c_544,plain,(
    ! [B_160] :
      ( r1_orders_2('#skF_2','#skF_1'(u1_orders_2('#skF_2'),B_160),'#skF_3')
      | '#skF_1'(u1_orders_2('#skF_2'),B_160) = '#skF_3'
      | r8_orders_1(u1_orders_2('#skF_2'),B_160)
      | ~ r2_hidden(B_160,k3_relat_1(u1_orders_2('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_81,c_50,c_52,c_463,c_540])).

tff(c_260,plain,(
    ! [B_105,C_106,A_107] :
      ( r2_hidden(k4_tarski(B_105,C_106),u1_orders_2(A_107))
      | ~ r1_orders_2(A_107,B_105,C_106)
      | ~ m1_subset_1(C_106,u1_struct_0(A_107))
      | ~ m1_subset_1(B_105,u1_struct_0(A_107))
      | ~ l1_orders_2(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_16,plain,(
    ! [A_12,B_18] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_12,B_18),B_18),A_12)
      | r8_orders_1(A_12,B_18)
      | ~ r2_hidden(B_18,k3_relat_1(A_12))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_272,plain,(
    ! [A_107,C_106] :
      ( r8_orders_1(u1_orders_2(A_107),C_106)
      | ~ r2_hidden(C_106,k3_relat_1(u1_orders_2(A_107)))
      | ~ v1_relat_1(u1_orders_2(A_107))
      | ~ r1_orders_2(A_107,'#skF_1'(u1_orders_2(A_107),C_106),C_106)
      | ~ m1_subset_1(C_106,u1_struct_0(A_107))
      | ~ m1_subset_1('#skF_1'(u1_orders_2(A_107),C_106),u1_struct_0(A_107))
      | ~ l1_orders_2(A_107) ) ),
    inference(resolution,[status(thm)],[c_260,c_16])).

tff(c_547,plain,
    ( ~ v1_relat_1(u1_orders_2('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_1'(u1_orders_2('#skF_2'),'#skF_3'),u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | '#skF_1'(u1_orders_2('#skF_2'),'#skF_3') = '#skF_3'
    | r8_orders_1(u1_orders_2('#skF_2'),'#skF_3')
    | ~ r2_hidden('#skF_3',k3_relat_1(u1_orders_2('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_544,c_272])).

tff(c_550,plain,
    ( ~ m1_subset_1('#skF_1'(u1_orders_2('#skF_2'),'#skF_3'),u1_struct_0('#skF_2'))
    | '#skF_1'(u1_orders_2('#skF_2'),'#skF_3') = '#skF_3'
    | r8_orders_1(u1_orders_2('#skF_2'),'#skF_3')
    | ~ r2_hidden('#skF_3',k3_relat_1(u1_orders_2('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_463,c_547])).

tff(c_551,plain,
    ( ~ m1_subset_1('#skF_1'(u1_orders_2('#skF_2'),'#skF_3'),u1_struct_0('#skF_2'))
    | ~ r2_hidden('#skF_3',k3_relat_1(u1_orders_2('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_464,c_550])).

tff(c_552,plain,(
    ~ r2_hidden('#skF_3',k3_relat_1(u1_orders_2('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_551])).

tff(c_555,plain,
    ( ~ r2_hidden('#skF_3',u1_struct_0('#skF_2'))
    | ~ v4_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v2_orders_2('#skF_2')
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_552])).

tff(c_563,plain,(
    ~ r2_hidden('#skF_3',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_81,c_50,c_52,c_555])).

tff(c_570,plain,
    ( v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_44,c_563])).

tff(c_573,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_570])).

tff(c_32,plain,(
    ! [A_32] :
      ( ~ v1_xboole_0(u1_struct_0(A_32))
      | ~ l1_struct_0(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_576,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_573,c_32])).

tff(c_579,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_576])).

tff(c_582,plain,(
    ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_579])).

tff(c_586,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_582])).

tff(c_588,plain,(
    r2_hidden('#skF_3',k3_relat_1(u1_orders_2('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_551])).

tff(c_587,plain,(
    ~ m1_subset_1('#skF_1'(u1_orders_2('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_551])).

tff(c_653,plain,
    ( r8_orders_1(u1_orders_2('#skF_2'),'#skF_3')
    | ~ r2_hidden('#skF_3',k3_relat_1(u1_orders_2('#skF_2')))
    | ~ v1_relat_1(u1_orders_2('#skF_2'))
    | ~ v4_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v2_orders_2('#skF_2')
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_325,c_587])).

tff(c_656,plain,(
    r8_orders_1(u1_orders_2('#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_81,c_50,c_52,c_463,c_588,c_653])).

tff(c_658,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_656])).

tff(c_659,plain,(
    ~ r2_hidden('#skF_3',u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_462])).

tff(c_663,plain,
    ( v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_44,c_659])).

tff(c_666,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_663])).

tff(c_669,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_666,c_32])).

tff(c_672,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_669])).

tff(c_675,plain,(
    ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_672])).

tff(c_679,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_675])).

tff(c_680,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_681,plain,(
    r8_orders_1(u1_orders_2('#skF_2'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_58,plain,
    ( ~ r2_orders_2('#skF_2','#skF_4','#skF_3')
    | ~ r8_orders_1(u1_orders_2('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_692,plain,(
    ~ r2_orders_2('#skF_2','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_681,c_58])).

tff(c_62,plain,
    ( m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ r8_orders_1(u1_orders_2('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_690,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_681,c_62])).

tff(c_836,plain,(
    ! [A_212,B_213,C_214] :
      ( r2_orders_2(A_212,B_213,C_214)
      | C_214 = B_213
      | ~ r1_orders_2(A_212,B_213,C_214)
      | ~ m1_subset_1(C_214,u1_struct_0(A_212))
      | ~ m1_subset_1(B_213,u1_struct_0(A_212))
      | ~ l1_orders_2(A_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_846,plain,(
    ! [B_213] :
      ( r2_orders_2('#skF_2',B_213,'#skF_3')
      | B_213 = '#skF_3'
      | ~ r1_orders_2('#skF_2',B_213,'#skF_3')
      | ~ m1_subset_1(B_213,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_46,c_836])).

tff(c_878,plain,(
    ! [B_216] :
      ( r2_orders_2('#skF_2',B_216,'#skF_3')
      | B_216 = '#skF_3'
      | ~ r1_orders_2('#skF_2',B_216,'#skF_3')
      | ~ m1_subset_1(B_216,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_846])).

tff(c_889,plain,
    ( r2_orders_2('#skF_2','#skF_4','#skF_3')
    | '#skF_3' = '#skF_4'
    | ~ r1_orders_2('#skF_2','#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_690,c_878])).

tff(c_897,plain,(
    ~ r1_orders_2('#skF_2','#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_680,c_692,c_889])).

tff(c_767,plain,(
    ! [B_196,A_197] :
      ( k3_relat_1(B_196) = A_197
      | ~ m1_subset_1(B_196,k1_zfmisc_1(k2_zfmisc_1(A_197,A_197)))
      | ~ v1_partfun1(B_196,A_197)
      | ~ v8_relat_2(B_196)
      | ~ v4_relat_2(B_196)
      | ~ v1_relat_2(B_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_930,plain,(
    ! [A_226] :
      ( k3_relat_1(u1_orders_2(A_226)) = u1_struct_0(A_226)
      | ~ v1_partfun1(u1_orders_2(A_226),u1_struct_0(A_226))
      | ~ v8_relat_2(u1_orders_2(A_226))
      | ~ v4_relat_2(u1_orders_2(A_226))
      | ~ v1_relat_2(u1_orders_2(A_226))
      | ~ l1_orders_2(A_226) ) ),
    inference(resolution,[status(thm)],[c_28,c_767])).

tff(c_936,plain,(
    ! [A_229] :
      ( k3_relat_1(u1_orders_2(A_229)) = u1_struct_0(A_229)
      | ~ v8_relat_2(u1_orders_2(A_229))
      | ~ v4_relat_2(u1_orders_2(A_229))
      | ~ v1_relat_2(u1_orders_2(A_229))
      | ~ l1_orders_2(A_229)
      | ~ v2_orders_2(A_229) ) ),
    inference(resolution,[status(thm)],[c_30,c_930])).

tff(c_941,plain,(
    ! [A_230] :
      ( k3_relat_1(u1_orders_2(A_230)) = u1_struct_0(A_230)
      | ~ v4_relat_2(u1_orders_2(A_230))
      | ~ v1_relat_2(u1_orders_2(A_230))
      | ~ l1_orders_2(A_230)
      | ~ v4_orders_2(A_230)
      | ~ v2_orders_2(A_230) ) ),
    inference(resolution,[status(thm)],[c_38,c_936])).

tff(c_946,plain,(
    ! [A_231] :
      ( k3_relat_1(u1_orders_2(A_231)) = u1_struct_0(A_231)
      | ~ v1_relat_2(u1_orders_2(A_231))
      | ~ v4_orders_2(A_231)
      | ~ l1_orders_2(A_231)
      | ~ v5_orders_2(A_231)
      | ~ v2_orders_2(A_231) ) ),
    inference(resolution,[status(thm)],[c_36,c_941])).

tff(c_950,plain,(
    ! [A_33] :
      ( k3_relat_1(u1_orders_2(A_33)) = u1_struct_0(A_33)
      | ~ v4_orders_2(A_33)
      | ~ v5_orders_2(A_33)
      | ~ v2_orders_2(A_33)
      | ~ l1_orders_2(A_33)
      | ~ v3_orders_2(A_33) ) ),
    inference(resolution,[status(thm)],[c_34,c_946])).

tff(c_704,plain,(
    ! [A_181] :
      ( m1_subset_1(u1_orders_2(A_181),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_181),u1_struct_0(A_181))))
      | ~ l1_orders_2(A_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_708,plain,(
    ! [A_181] :
      ( v1_relat_1(u1_orders_2(A_181))
      | ~ l1_orders_2(A_181) ) ),
    inference(resolution,[status(thm)],[c_704,c_4])).

tff(c_952,plain,(
    ! [A_232] :
      ( k3_relat_1(u1_orders_2(A_232)) = u1_struct_0(A_232)
      | ~ v4_orders_2(A_232)
      | ~ v5_orders_2(A_232)
      | ~ v2_orders_2(A_232)
      | ~ l1_orders_2(A_232)
      | ~ v3_orders_2(A_232) ) ),
    inference(resolution,[status(thm)],[c_34,c_946])).

tff(c_14,plain,(
    ! [B_18,A_12] :
      ( r2_hidden(B_18,k3_relat_1(A_12))
      | ~ r8_orders_1(A_12,B_18)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_991,plain,(
    ! [B_235,A_236] :
      ( r2_hidden(B_235,u1_struct_0(A_236))
      | ~ r8_orders_1(u1_orders_2(A_236),B_235)
      | ~ v1_relat_1(u1_orders_2(A_236))
      | ~ v4_orders_2(A_236)
      | ~ v5_orders_2(A_236)
      | ~ v2_orders_2(A_236)
      | ~ l1_orders_2(A_236)
      | ~ v3_orders_2(A_236) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_952,c_14])).

tff(c_994,plain,
    ( r2_hidden('#skF_3',u1_struct_0('#skF_2'))
    | ~ v1_relat_1(u1_orders_2('#skF_2'))
    | ~ v4_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v2_orders_2('#skF_2')
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_681,c_991])).

tff(c_997,plain,
    ( r2_hidden('#skF_3',u1_struct_0('#skF_2'))
    | ~ v1_relat_1(u1_orders_2('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_81,c_50,c_52,c_994])).

tff(c_998,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_997])).

tff(c_1012,plain,(
    ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_708,c_998])).

tff(c_1016,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1012])).

tff(c_1018,plain,(
    v1_relat_1(u1_orders_2('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_997])).

tff(c_972,plain,(
    ! [A_232,B_18] :
      ( '#skF_1'(u1_orders_2(A_232),B_18) != B_18
      | r8_orders_1(u1_orders_2(A_232),B_18)
      | ~ r2_hidden(B_18,u1_struct_0(A_232))
      | ~ v1_relat_1(u1_orders_2(A_232))
      | ~ v4_orders_2(A_232)
      | ~ v5_orders_2(A_232)
      | ~ v2_orders_2(A_232)
      | ~ l1_orders_2(A_232)
      | ~ v3_orders_2(A_232) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_952,c_18])).

tff(c_12,plain,(
    ! [C_21,B_18,A_12] :
      ( r2_hidden(k4_tarski(C_21,B_18),A_12)
      | C_21 = B_18
      | ~ r2_hidden(C_21,k3_relat_1(A_12))
      | ~ r8_orders_1(A_12,B_18)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_910,plain,(
    ! [A_220,B_221,C_222] :
      ( r1_orders_2(A_220,B_221,C_222)
      | ~ r2_hidden(k4_tarski(B_221,C_222),u1_orders_2(A_220))
      | ~ m1_subset_1(C_222,u1_struct_0(A_220))
      | ~ m1_subset_1(B_221,u1_struct_0(A_220))
      | ~ l1_orders_2(A_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1095,plain,(
    ! [A_251,C_252,B_253] :
      ( r1_orders_2(A_251,C_252,B_253)
      | ~ m1_subset_1(B_253,u1_struct_0(A_251))
      | ~ m1_subset_1(C_252,u1_struct_0(A_251))
      | ~ l1_orders_2(A_251)
      | C_252 = B_253
      | ~ r2_hidden(C_252,k3_relat_1(u1_orders_2(A_251)))
      | ~ r8_orders_1(u1_orders_2(A_251),B_253)
      | ~ v1_relat_1(u1_orders_2(A_251)) ) ),
    inference(resolution,[status(thm)],[c_12,c_910])).

tff(c_1128,plain,(
    ! [A_256,B_257,B_258] :
      ( r1_orders_2(A_256,B_257,B_258)
      | ~ m1_subset_1(B_258,u1_struct_0(A_256))
      | ~ m1_subset_1(B_257,u1_struct_0(A_256))
      | ~ l1_orders_2(A_256)
      | B_258 = B_257
      | ~ r8_orders_1(u1_orders_2(A_256),B_258)
      | ~ r8_orders_1(u1_orders_2(A_256),B_257)
      | ~ v1_relat_1(u1_orders_2(A_256)) ) ),
    inference(resolution,[status(thm)],[c_14,c_1095])).

tff(c_1135,plain,(
    ! [B_257] :
      ( r1_orders_2('#skF_2',B_257,'#skF_3')
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_257,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | B_257 = '#skF_3'
      | ~ r8_orders_1(u1_orders_2('#skF_2'),B_257)
      | ~ v1_relat_1(u1_orders_2('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_681,c_1128])).

tff(c_1141,plain,(
    ! [B_259] :
      ( r1_orders_2('#skF_2',B_259,'#skF_3')
      | ~ m1_subset_1(B_259,u1_struct_0('#skF_2'))
      | B_259 = '#skF_3'
      | ~ r8_orders_1(u1_orders_2('#skF_2'),B_259) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1018,c_48,c_46,c_1135])).

tff(c_1145,plain,(
    ! [B_18] :
      ( r1_orders_2('#skF_2',B_18,'#skF_3')
      | ~ m1_subset_1(B_18,u1_struct_0('#skF_2'))
      | B_18 = '#skF_3'
      | '#skF_1'(u1_orders_2('#skF_2'),B_18) != B_18
      | ~ r2_hidden(B_18,u1_struct_0('#skF_2'))
      | ~ v1_relat_1(u1_orders_2('#skF_2'))
      | ~ v4_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v2_orders_2('#skF_2')
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_972,c_1141])).

tff(c_1163,plain,(
    ! [B_260] :
      ( r1_orders_2('#skF_2',B_260,'#skF_3')
      | ~ m1_subset_1(B_260,u1_struct_0('#skF_2'))
      | B_260 = '#skF_3'
      | '#skF_1'(u1_orders_2('#skF_2'),B_260) != B_260
      | ~ r2_hidden(B_260,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_81,c_50,c_52,c_1018,c_1145])).

tff(c_1180,plain,(
    ! [A_40] :
      ( r1_orders_2('#skF_2',A_40,'#skF_3')
      | A_40 = '#skF_3'
      | '#skF_1'(u1_orders_2('#skF_2'),A_40) != A_40
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ m1_subset_1(A_40,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_44,c_1163])).

tff(c_1181,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1180])).

tff(c_1184,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_1181,c_32])).

tff(c_1187,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1184])).

tff(c_1190,plain,(
    ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_1187])).

tff(c_1194,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1190])).

tff(c_1196,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1180])).

tff(c_1407,plain,(
    ! [A_295,A_296,B_297] :
      ( r1_orders_2(A_295,A_296,B_297)
      | ~ m1_subset_1(B_297,u1_struct_0(A_295))
      | ~ m1_subset_1(A_296,u1_struct_0(A_295))
      | ~ l1_orders_2(A_295)
      | B_297 = A_296
      | ~ r8_orders_1(u1_orders_2(A_295),B_297)
      | ~ v1_relat_1(u1_orders_2(A_295))
      | v1_xboole_0(k3_relat_1(u1_orders_2(A_295)))
      | ~ m1_subset_1(A_296,k3_relat_1(u1_orders_2(A_295))) ) ),
    inference(resolution,[status(thm)],[c_44,c_1095])).

tff(c_1416,plain,(
    ! [A_296] :
      ( r1_orders_2('#skF_2',A_296,'#skF_3')
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(A_296,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | A_296 = '#skF_3'
      | ~ v1_relat_1(u1_orders_2('#skF_2'))
      | v1_xboole_0(k3_relat_1(u1_orders_2('#skF_2')))
      | ~ m1_subset_1(A_296,k3_relat_1(u1_orders_2('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_681,c_1407])).

tff(c_1422,plain,(
    ! [A_296] :
      ( r1_orders_2('#skF_2',A_296,'#skF_3')
      | ~ m1_subset_1(A_296,u1_struct_0('#skF_2'))
      | A_296 = '#skF_3'
      | v1_xboole_0(k3_relat_1(u1_orders_2('#skF_2')))
      | ~ m1_subset_1(A_296,k3_relat_1(u1_orders_2('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1018,c_48,c_46,c_1416])).

tff(c_1430,plain,(
    v1_xboole_0(k3_relat_1(u1_orders_2('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1422])).

tff(c_1433,plain,
    ( v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ v4_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v2_orders_2('#skF_2')
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_950,c_1430])).

tff(c_1435,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_81,c_50,c_52,c_1433])).

tff(c_1437,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1196,c_1435])).

tff(c_1457,plain,(
    ! [A_301] :
      ( r1_orders_2('#skF_2',A_301,'#skF_3')
      | ~ m1_subset_1(A_301,u1_struct_0('#skF_2'))
      | A_301 = '#skF_3'
      | ~ m1_subset_1(A_301,k3_relat_1(u1_orders_2('#skF_2'))) ) ),
    inference(splitRight,[status(thm)],[c_1422])).

tff(c_1468,plain,(
    ! [A_301] :
      ( r1_orders_2('#skF_2',A_301,'#skF_3')
      | ~ m1_subset_1(A_301,u1_struct_0('#skF_2'))
      | A_301 = '#skF_3'
      | ~ m1_subset_1(A_301,u1_struct_0('#skF_2'))
      | ~ v4_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v2_orders_2('#skF_2')
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_950,c_1457])).

tff(c_1497,plain,(
    ! [A_302] :
      ( r1_orders_2('#skF_2',A_302,'#skF_3')
      | A_302 = '#skF_3'
      | ~ m1_subset_1(A_302,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_81,c_50,c_52,c_1468])).

tff(c_1520,plain,
    ( r1_orders_2('#skF_2','#skF_4','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_690,c_1497])).

tff(c_1534,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_680,c_897,c_1520])).

%------------------------------------------------------------------------------
