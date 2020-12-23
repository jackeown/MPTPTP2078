%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:24 EST 2020

% Result     : Theorem 4.83s
% Output     : CNFRefutation 5.20s
% Verified   : 
% Statistics : Number of formulae       :  288 (22974 expanded)
%              Number of leaves         :   49 (8007 expanded)
%              Depth                    :   27
%              Number of atoms          :  634 (68932 expanded)
%              Number of equality atoms :  176 (21392 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

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

tff(f_173,negated_conjecture,(
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

tff(f_129,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_137,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_109,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_149,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v2_funct_1(A)
            & r1_tarski(B,k1_relat_1(A)) )
         => k9_relat_1(k2_funct_1(A),k9_relat_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t177_funct_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_125,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(C)
          & k2_relset_1(A,B,C) = B )
       => ( v1_funct_1(k2_funct_1(C))
          & v1_funct_2(k2_funct_1(C),B,A)
          & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k9_relat_1(B,A) = k10_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_60,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_62,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_66,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_70,plain,(
    ! [A_48] :
      ( u1_struct_0(A_48) = k2_struct_0(A_48)
      | ~ l1_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_78,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_70])).

tff(c_77,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_70])).

tff(c_56,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_102,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_77,c_56])).

tff(c_1440,plain,(
    ! [A_222,B_223,C_224] :
      ( k2_relset_1(A_222,B_223,C_224) = k2_relat_1(C_224)
      | ~ m1_subset_1(C_224,k1_zfmisc_1(k2_zfmisc_1(A_222,B_223))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1444,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_102,c_1440])).

tff(c_54,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_97,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_77,c_54])).

tff(c_1445,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1444,c_97])).

tff(c_46,plain,(
    ! [A_37] :
      ( ~ v1_xboole_0(k2_struct_0(A_37))
      | ~ l1_struct_0(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_1460,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1445,c_46])).

tff(c_1464,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1460])).

tff(c_1465,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1464])).

tff(c_10,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_112,plain,(
    ! [B_53,A_54] :
      ( v1_relat_1(B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_54))
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_115,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_102,c_112])).

tff(c_118,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_115])).

tff(c_1380,plain,(
    ! [C_206,A_207,B_208] :
      ( v4_relat_1(C_206,A_207)
      | ~ m1_subset_1(C_206,k1_zfmisc_1(k2_zfmisc_1(A_207,B_208))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1384,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_102,c_1380])).

tff(c_1423,plain,(
    ! [B_217,A_218] :
      ( k1_relat_1(B_217) = A_218
      | ~ v1_partfun1(B_217,A_218)
      | ~ v4_relat_1(B_217,A_218)
      | ~ v1_relat_1(B_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1426,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1384,c_1423])).

tff(c_1429,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_1426])).

tff(c_1430,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1429])).

tff(c_58,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_83,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_58])).

tff(c_84,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_83])).

tff(c_1455,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1445,c_84])).

tff(c_1454,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1445,c_102])).

tff(c_1527,plain,(
    ! [C_227,A_228,B_229] :
      ( v1_partfun1(C_227,A_228)
      | ~ v1_funct_2(C_227,A_228,B_229)
      | ~ v1_funct_1(C_227)
      | ~ m1_subset_1(C_227,k1_zfmisc_1(k2_zfmisc_1(A_228,B_229)))
      | v1_xboole_0(B_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1530,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1454,c_1527])).

tff(c_1533,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1455,c_1530])).

tff(c_1535,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1465,c_1430,c_1533])).

tff(c_1536,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1429])).

tff(c_1538,plain,(
    ! [A_230,B_231,C_232] :
      ( k2_relset_1(A_230,B_231,C_232) = k2_relat_1(C_232)
      | ~ m1_subset_1(C_232,k1_zfmisc_1(k2_zfmisc_1(A_230,B_231))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1542,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_102,c_1538])).

tff(c_1601,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1536,c_1542])).

tff(c_1548,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1536,c_97])).

tff(c_1631,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1601,c_1548])).

tff(c_1549,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1536,c_84])).

tff(c_1634,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1631,c_1549])).

tff(c_1633,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1631,c_1601])).

tff(c_52,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_1547,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1536,c_102])).

tff(c_1632,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1631,c_1547])).

tff(c_2260,plain,(
    ! [A_309,B_310,C_311] :
      ( k2_tops_2(A_309,B_310,C_311) = k2_funct_1(C_311)
      | ~ v2_funct_1(C_311)
      | k2_relset_1(A_309,B_310,C_311) != B_310
      | ~ m1_subset_1(C_311,k1_zfmisc_1(k2_zfmisc_1(A_309,B_310)))
      | ~ v1_funct_2(C_311,A_309,B_310)
      | ~ v1_funct_1(C_311) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_2263,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1632,c_2260])).

tff(c_2266,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1634,c_1633,c_52,c_2263])).

tff(c_181,plain,(
    ! [A_71,B_72,C_73] :
      ( k2_relset_1(A_71,B_72,C_73) = k2_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_185,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_102,c_181])).

tff(c_186,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_97])).

tff(c_201,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_46])).

tff(c_205,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_201])).

tff(c_206,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_205])).

tff(c_121,plain,(
    ! [C_55,A_56,B_57] :
      ( v4_relat_1(C_55,A_56)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_125,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_102,c_121])).

tff(c_164,plain,(
    ! [B_66,A_67] :
      ( k1_relat_1(B_66) = A_67
      | ~ v1_partfun1(B_66,A_67)
      | ~ v4_relat_1(B_66,A_67)
      | ~ v1_relat_1(B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_167,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_125,c_164])).

tff(c_170,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_167])).

tff(c_171,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_170])).

tff(c_196,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_84])).

tff(c_195,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_102])).

tff(c_263,plain,(
    ! [C_76,A_77,B_78] :
      ( v1_partfun1(C_76,A_77)
      | ~ v1_funct_2(C_76,A_77,B_78)
      | ~ v1_funct_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78)))
      | v1_xboole_0(B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_266,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_195,c_263])).

tff(c_269,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_196,c_266])).

tff(c_271,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_206,c_171,c_269])).

tff(c_272,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_170])).

tff(c_278,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_102])).

tff(c_360,plain,(
    ! [A_82,B_83,C_84] :
      ( k2_relset_1(A_82,B_83,C_84) = k2_relat_1(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_364,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_278,c_360])).

tff(c_279,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_97])).

tff(c_365,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_364,c_279])).

tff(c_280,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_84])).

tff(c_372,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_365,c_280])).

tff(c_370,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_365,c_364])).

tff(c_373,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_365,c_278])).

tff(c_1280,plain,(
    ! [A_188,B_189,C_190] :
      ( k2_tops_2(A_188,B_189,C_190) = k2_funct_1(C_190)
      | ~ v2_funct_1(C_190)
      | k2_relset_1(A_188,B_189,C_190) != B_189
      | ~ m1_subset_1(C_190,k1_zfmisc_1(k2_zfmisc_1(A_188,B_189)))
      | ~ v1_funct_2(C_190,A_188,B_189)
      | ~ v1_funct_1(C_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_1283,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_373,c_1280])).

tff(c_1286,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_372,c_370,c_52,c_1283])).

tff(c_50,plain,
    ( k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_119,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_78,c_77,c_77,c_78,c_78,c_77,c_77,c_50])).

tff(c_120,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_119])).

tff(c_274,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_272,c_120])).

tff(c_441,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_365,c_365,c_365,c_274])).

tff(c_1288,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1286,c_441])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_138,plain,(
    ! [B_60,A_61] :
      ( k7_relat_1(B_60,A_61) = B_60
      | ~ v4_relat_1(B_60,A_61)
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_141,plain,
    ( k7_relat_1('#skF_3',k2_struct_0('#skF_1')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_125,c_138])).

tff(c_144,plain,(
    k7_relat_1('#skF_3',k2_struct_0('#skF_1')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_141])).

tff(c_276,plain,(
    k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_144])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( k2_relat_1(k7_relat_1(B_9,A_8)) = k9_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_318,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_276,c_12])).

tff(c_322,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_318])).

tff(c_450,plain,(
    ! [A_90,B_91] :
      ( k9_relat_1(k2_funct_1(A_90),k9_relat_1(A_90,B_91)) = B_91
      | ~ r1_tarski(B_91,k1_relat_1(A_90))
      | ~ v2_funct_1(A_90)
      | ~ v1_funct_1(A_90)
      | ~ v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_465,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_322,c_450])).

tff(c_469,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_60,c_52,c_6,c_465])).

tff(c_126,plain,(
    ! [B_58,A_59] :
      ( k2_relat_1(k7_relat_1(B_58,A_59)) = k9_relat_1(B_58,A_59)
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_14,plain,(
    ! [A_10] :
      ( k10_relat_1(A_10,k2_relat_1(A_10)) = k1_relat_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_489,plain,(
    ! [B_93,A_94] :
      ( k10_relat_1(k7_relat_1(B_93,A_94),k9_relat_1(B_93,A_94)) = k1_relat_1(k7_relat_1(B_93,A_94))
      | ~ v1_relat_1(k7_relat_1(B_93,A_94))
      | ~ v1_relat_1(B_93) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_14])).

tff(c_501,plain,
    ( k10_relat_1(k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')),k1_relat_1('#skF_3')) = k1_relat_1(k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')))
    | ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_469,c_489])).

tff(c_541,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_501])).

tff(c_558,plain,(
    ! [C_104,B_105,A_106] :
      ( m1_subset_1(k2_funct_1(C_104),k1_zfmisc_1(k2_zfmisc_1(B_105,A_106)))
      | k2_relset_1(A_106,B_105,C_104) != B_105
      | ~ v2_funct_1(C_104)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_106,B_105)))
      | ~ v1_funct_2(C_104,A_106,B_105)
      | ~ v1_funct_1(C_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_8,plain,(
    ! [B_5,A_3] :
      ( v1_relat_1(B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_3))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_585,plain,(
    ! [C_104,B_105,A_106] :
      ( v1_relat_1(k2_funct_1(C_104))
      | ~ v1_relat_1(k2_zfmisc_1(B_105,A_106))
      | k2_relset_1(A_106,B_105,C_104) != B_105
      | ~ v2_funct_1(C_104)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_106,B_105)))
      | ~ v1_funct_2(C_104,A_106,B_105)
      | ~ v1_funct_1(C_104) ) ),
    inference(resolution,[status(thm)],[c_558,c_8])).

tff(c_602,plain,(
    ! [C_107,A_108,B_109] :
      ( v1_relat_1(k2_funct_1(C_107))
      | k2_relset_1(A_108,B_109,C_107) != B_109
      | ~ v2_funct_1(C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109)))
      | ~ v1_funct_2(C_107,A_108,B_109)
      | ~ v1_funct_1(C_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_585])).

tff(c_608,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_373,c_602])).

tff(c_612,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_372,c_52,c_370,c_608])).

tff(c_614,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_541,c_612])).

tff(c_616,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_501])).

tff(c_994,plain,(
    ! [C_161,B_162,A_163] :
      ( m1_subset_1(k2_funct_1(C_161),k1_zfmisc_1(k2_zfmisc_1(B_162,A_163)))
      | k2_relset_1(A_163,B_162,C_161) != B_162
      | ~ v2_funct_1(C_161)
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(A_163,B_162)))
      | ~ v1_funct_2(C_161,A_163,B_162)
      | ~ v1_funct_1(C_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_24,plain,(
    ! [C_20,A_18,B_19] :
      ( v4_relat_1(C_20,A_18)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1055,plain,(
    ! [C_170,B_171,A_172] :
      ( v4_relat_1(k2_funct_1(C_170),B_171)
      | k2_relset_1(A_172,B_171,C_170) != B_171
      | ~ v2_funct_1(C_170)
      | ~ m1_subset_1(C_170,k1_zfmisc_1(k2_zfmisc_1(A_172,B_171)))
      | ~ v1_funct_2(C_170,A_172,B_171)
      | ~ v1_funct_1(C_170) ) ),
    inference(resolution,[status(thm)],[c_994,c_24])).

tff(c_1061,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_373,c_1055])).

tff(c_1065,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_372,c_52,c_370,c_1061])).

tff(c_16,plain,(
    ! [B_12,A_11] :
      ( k7_relat_1(B_12,A_11) = B_12
      | ~ v4_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1071,plain,
    ( k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1065,c_16])).

tff(c_1077,plain,(
    k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_616,c_1071])).

tff(c_1087,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1077,c_12])).

tff(c_1093,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_616,c_469,c_1087])).

tff(c_422,plain,(
    ! [B_85,A_86] :
      ( k10_relat_1(k2_funct_1(B_85),A_86) = k9_relat_1(B_85,A_86)
      | ~ v2_funct_1(B_85)
      | ~ v1_funct_1(B_85)
      | ~ v1_relat_1(B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_436,plain,(
    ! [B_85] :
      ( k9_relat_1(B_85,k2_relat_1(k2_funct_1(B_85))) = k1_relat_1(k2_funct_1(B_85))
      | ~ v2_funct_1(B_85)
      | ~ v1_funct_1(B_85)
      | ~ v1_relat_1(B_85)
      | ~ v1_relat_1(k2_funct_1(B_85)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_422])).

tff(c_1109,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1093,c_436])).

tff(c_1116,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_616,c_118,c_60,c_52,c_322,c_1109])).

tff(c_752,plain,(
    ! [C_131,B_132,A_133] :
      ( m1_subset_1(k2_funct_1(C_131),k1_zfmisc_1(k2_zfmisc_1(B_132,A_133)))
      | k2_relset_1(A_133,B_132,C_131) != B_132
      | ~ v2_funct_1(C_131)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_133,B_132)))
      | ~ v1_funct_2(C_131,A_133,B_132)
      | ~ v1_funct_1(C_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_813,plain,(
    ! [C_140,B_141,A_142] :
      ( v4_relat_1(k2_funct_1(C_140),B_141)
      | k2_relset_1(A_142,B_141,C_140) != B_141
      | ~ v2_funct_1(C_140)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_142,B_141)))
      | ~ v1_funct_2(C_140,A_142,B_141)
      | ~ v1_funct_1(C_140) ) ),
    inference(resolution,[status(thm)],[c_752,c_24])).

tff(c_819,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_373,c_813])).

tff(c_823,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_372,c_52,c_370,c_819])).

tff(c_829,plain,
    ( k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_823,c_16])).

tff(c_835,plain,(
    k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_616,c_829])).

tff(c_845,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_835,c_12])).

tff(c_851,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_616,c_469,c_845])).

tff(c_856,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_851,c_436])).

tff(c_863,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_616,c_118,c_60,c_52,c_322,c_856])).

tff(c_533,plain,(
    ! [C_95,A_96,B_97] :
      ( v1_funct_1(k2_funct_1(C_95))
      | k2_relset_1(A_96,B_97,C_95) != B_97
      | ~ v2_funct_1(C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97)))
      | ~ v1_funct_2(C_95,A_96,B_97)
      | ~ v1_funct_1(C_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_536,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_373,c_533])).

tff(c_539,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_372,c_52,c_370,c_536])).

tff(c_20,plain,(
    ! [A_15,B_17] :
      ( k9_relat_1(k2_funct_1(A_15),k9_relat_1(A_15,B_17)) = B_17
      | ~ r1_tarski(B_17,k1_relat_1(A_15))
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_473,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ r1_tarski(k2_relat_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_469,c_20])).

tff(c_618,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ r1_tarski(k2_relat_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_539,c_473])).

tff(c_619,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_618])).

tff(c_621,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_616,c_619])).

tff(c_622,plain,
    ( ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ r1_tarski(k2_relat_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')))
    | k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_618])).

tff(c_625,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_622])).

tff(c_867,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_863,c_625])).

tff(c_870,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_867])).

tff(c_872,plain,(
    r1_tarski(k2_relat_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_622])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_875,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_872,c_2])).

tff(c_977,plain,(
    ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),k2_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_875])).

tff(c_1120,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1116,c_977])).

tff(c_1124,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1120])).

tff(c_1125,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_875])).

tff(c_1293,plain,(
    ! [C_191,B_192,A_193] :
      ( m1_subset_1(k2_funct_1(C_191),k1_zfmisc_1(k2_zfmisc_1(B_192,A_193)))
      | k2_relset_1(A_193,B_192,C_191) != B_192
      | ~ v2_funct_1(C_191)
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(A_193,B_192)))
      | ~ v1_funct_2(C_191,A_193,B_192)
      | ~ v1_funct_1(C_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_26,plain,(
    ! [A_21,B_22,C_23] :
      ( k1_relset_1(A_21,B_22,C_23) = k1_relat_1(C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1365,plain,(
    ! [B_203,A_204,C_205] :
      ( k1_relset_1(B_203,A_204,k2_funct_1(C_205)) = k1_relat_1(k2_funct_1(C_205))
      | k2_relset_1(A_204,B_203,C_205) != B_203
      | ~ v2_funct_1(C_205)
      | ~ m1_subset_1(C_205,k1_zfmisc_1(k2_zfmisc_1(A_204,B_203)))
      | ~ v1_funct_2(C_205,A_204,B_203)
      | ~ v1_funct_1(C_205) ) ),
    inference(resolution,[status(thm)],[c_1293,c_26])).

tff(c_1371,plain,
    ( k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_373,c_1365])).

tff(c_1375,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_372,c_52,c_370,c_1125,c_1371])).

tff(c_1377,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1288,c_1375])).

tff(c_1378,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_119])).

tff(c_1545,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1536,c_1536,c_1536,c_1378])).

tff(c_1708,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1631,c_1631,c_1545])).

tff(c_2267,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2266,c_1708])).

tff(c_1744,plain,(
    ! [C_243,A_244,B_245] :
      ( v1_funct_1(k2_funct_1(C_243))
      | k2_relset_1(A_244,B_245,C_243) != B_245
      | ~ v2_funct_1(C_243)
      | ~ m1_subset_1(C_243,k1_zfmisc_1(k2_zfmisc_1(A_244,B_245)))
      | ~ v1_funct_2(C_243,A_244,B_245)
      | ~ v1_funct_1(C_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1747,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1632,c_1744])).

tff(c_1750,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1634,c_52,c_1633,c_1747])).

tff(c_1402,plain,(
    ! [B_214,A_215] :
      ( k7_relat_1(B_214,A_215) = B_214
      | ~ v4_relat_1(B_214,A_215)
      | ~ v1_relat_1(B_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1405,plain,
    ( k7_relat_1('#skF_3',k2_struct_0('#skF_1')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1384,c_1402])).

tff(c_1408,plain,(
    k7_relat_1('#skF_3',k2_struct_0('#skF_1')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_1405])).

tff(c_1544,plain,(
    k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1536,c_1408])).

tff(c_1587,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1544,c_12])).

tff(c_1591,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_1587])).

tff(c_1709,plain,(
    ! [A_238,B_239] :
      ( k9_relat_1(k2_funct_1(A_238),k9_relat_1(A_238,B_239)) = B_239
      | ~ r1_tarski(B_239,k1_relat_1(A_238))
      | ~ v2_funct_1(A_238)
      | ~ v1_funct_1(A_238)
      | ~ v1_relat_1(A_238) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1724,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1591,c_1709])).

tff(c_1728,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_60,c_52,c_6,c_1724])).

tff(c_1732,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ r1_tarski(k2_relat_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1728,c_20])).

tff(c_1809,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ r1_tarski(k2_relat_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1750,c_1732])).

tff(c_1810,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1809])).

tff(c_1835,plain,(
    ! [C_255,B_256,A_257] :
      ( m1_subset_1(k2_funct_1(C_255),k1_zfmisc_1(k2_zfmisc_1(B_256,A_257)))
      | k2_relset_1(A_257,B_256,C_255) != B_256
      | ~ v2_funct_1(C_255)
      | ~ m1_subset_1(C_255,k1_zfmisc_1(k2_zfmisc_1(A_257,B_256)))
      | ~ v1_funct_2(C_255,A_257,B_256)
      | ~ v1_funct_1(C_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1862,plain,(
    ! [C_255,B_256,A_257] :
      ( v1_relat_1(k2_funct_1(C_255))
      | ~ v1_relat_1(k2_zfmisc_1(B_256,A_257))
      | k2_relset_1(A_257,B_256,C_255) != B_256
      | ~ v2_funct_1(C_255)
      | ~ m1_subset_1(C_255,k1_zfmisc_1(k2_zfmisc_1(A_257,B_256)))
      | ~ v1_funct_2(C_255,A_257,B_256)
      | ~ v1_funct_1(C_255) ) ),
    inference(resolution,[status(thm)],[c_1835,c_8])).

tff(c_1874,plain,(
    ! [C_258,A_259,B_260] :
      ( v1_relat_1(k2_funct_1(C_258))
      | k2_relset_1(A_259,B_260,C_258) != B_260
      | ~ v2_funct_1(C_258)
      | ~ m1_subset_1(C_258,k1_zfmisc_1(k2_zfmisc_1(A_259,B_260)))
      | ~ v1_funct_2(C_258,A_259,B_260)
      | ~ v1_funct_1(C_258) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1862])).

tff(c_1880,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1632,c_1874])).

tff(c_1884,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1634,c_52,c_1633,c_1880])).

tff(c_1886,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1810,c_1884])).

tff(c_1888,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1809])).

tff(c_2282,plain,(
    ! [C_312,B_313,A_314] :
      ( m1_subset_1(k2_funct_1(C_312),k1_zfmisc_1(k2_zfmisc_1(B_313,A_314)))
      | k2_relset_1(A_314,B_313,C_312) != B_313
      | ~ v2_funct_1(C_312)
      | ~ m1_subset_1(C_312,k1_zfmisc_1(k2_zfmisc_1(A_314,B_313)))
      | ~ v1_funct_2(C_312,A_314,B_313)
      | ~ v1_funct_1(C_312) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_2343,plain,(
    ! [C_321,B_322,A_323] :
      ( v4_relat_1(k2_funct_1(C_321),B_322)
      | k2_relset_1(A_323,B_322,C_321) != B_322
      | ~ v2_funct_1(C_321)
      | ~ m1_subset_1(C_321,k1_zfmisc_1(k2_zfmisc_1(A_323,B_322)))
      | ~ v1_funct_2(C_321,A_323,B_322)
      | ~ v1_funct_1(C_321) ) ),
    inference(resolution,[status(thm)],[c_2282,c_24])).

tff(c_2349,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1632,c_2343])).

tff(c_2353,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1634,c_52,c_1633,c_2349])).

tff(c_2359,plain,
    ( k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2353,c_16])).

tff(c_2365,plain,(
    k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1888,c_2359])).

tff(c_2375,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2365,c_12])).

tff(c_2381,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1888,c_1728,c_2375])).

tff(c_1651,plain,(
    ! [B_236,A_237] :
      ( k10_relat_1(k2_funct_1(B_236),A_237) = k9_relat_1(B_236,A_237)
      | ~ v2_funct_1(B_236)
      | ~ v1_funct_1(B_236)
      | ~ v1_relat_1(B_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1665,plain,(
    ! [B_236] :
      ( k9_relat_1(B_236,k2_relat_1(k2_funct_1(B_236))) = k1_relat_1(k2_funct_1(B_236))
      | ~ v2_funct_1(B_236)
      | ~ v1_funct_1(B_236)
      | ~ v1_relat_1(B_236)
      | ~ v1_relat_1(k2_funct_1(B_236)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1651])).

tff(c_2387,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2381,c_1665])).

tff(c_2394,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1888,c_118,c_60,c_52,c_1591,c_2387])).

tff(c_2017,plain,(
    ! [C_279,B_280,A_281] :
      ( m1_subset_1(k2_funct_1(C_279),k1_zfmisc_1(k2_zfmisc_1(B_280,A_281)))
      | k2_relset_1(A_281,B_280,C_279) != B_280
      | ~ v2_funct_1(C_279)
      | ~ m1_subset_1(C_279,k1_zfmisc_1(k2_zfmisc_1(A_281,B_280)))
      | ~ v1_funct_2(C_279,A_281,B_280)
      | ~ v1_funct_1(C_279) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_2078,plain,(
    ! [C_288,B_289,A_290] :
      ( v4_relat_1(k2_funct_1(C_288),B_289)
      | k2_relset_1(A_290,B_289,C_288) != B_289
      | ~ v2_funct_1(C_288)
      | ~ m1_subset_1(C_288,k1_zfmisc_1(k2_zfmisc_1(A_290,B_289)))
      | ~ v1_funct_2(C_288,A_290,B_289)
      | ~ v1_funct_1(C_288) ) ),
    inference(resolution,[status(thm)],[c_2017,c_24])).

tff(c_2084,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1632,c_2078])).

tff(c_2088,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1634,c_52,c_1633,c_2084])).

tff(c_2094,plain,
    ( k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2088,c_16])).

tff(c_2100,plain,(
    k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1888,c_2094])).

tff(c_2110,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2100,c_12])).

tff(c_2116,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1888,c_1728,c_2110])).

tff(c_2121,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2116,c_1665])).

tff(c_2128,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1888,c_118,c_60,c_52,c_1591,c_2121])).

tff(c_1887,plain,
    ( ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ r1_tarski(k2_relat_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')))
    | k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1809])).

tff(c_1889,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_1887])).

tff(c_2132,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2128,c_1889])).

tff(c_2135,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2132])).

tff(c_2137,plain,(
    r1_tarski(k2_relat_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_1887])).

tff(c_2140,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2137,c_2])).

tff(c_2281,plain,(
    ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),k2_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2140])).

tff(c_2398,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2394,c_2281])).

tff(c_2402,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2398])).

tff(c_2403,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_2140])).

tff(c_34,plain,(
    ! [B_32] :
      ( v1_partfun1(B_32,k1_relat_1(B_32))
      | ~ v4_relat_1(B_32,k1_relat_1(B_32))
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2410,plain,
    ( v1_partfun1(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')))
    | ~ v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2403,c_34])).

tff(c_2414,plain,
    ( v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1888,c_2403,c_2410])).

tff(c_2456,plain,(
    ~ v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2414])).

tff(c_2417,plain,(
    ! [C_324,B_325,A_326] :
      ( m1_subset_1(k2_funct_1(C_324),k1_zfmisc_1(k2_zfmisc_1(B_325,A_326)))
      | k2_relset_1(A_326,B_325,C_324) != B_325
      | ~ v2_funct_1(C_324)
      | ~ m1_subset_1(C_324,k1_zfmisc_1(k2_zfmisc_1(A_326,B_325)))
      | ~ v1_funct_2(C_324,A_326,B_325)
      | ~ v1_funct_1(C_324) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_2479,plain,(
    ! [C_333,B_334,A_335] :
      ( v4_relat_1(k2_funct_1(C_333),B_334)
      | k2_relset_1(A_335,B_334,C_333) != B_334
      | ~ v2_funct_1(C_333)
      | ~ m1_subset_1(C_333,k1_zfmisc_1(k2_zfmisc_1(A_335,B_334)))
      | ~ v1_funct_2(C_333,A_335,B_334)
      | ~ v1_funct_1(C_333) ) ),
    inference(resolution,[status(thm)],[c_2417,c_24])).

tff(c_2485,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1632,c_2479])).

tff(c_2489,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1634,c_52,c_1633,c_2485])).

tff(c_2491,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2456,c_2489])).

tff(c_2493,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2414])).

tff(c_2499,plain,
    ( k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2493,c_16])).

tff(c_2505,plain,(
    k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1888,c_2499])).

tff(c_2516,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2505,c_12])).

tff(c_2522,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1888,c_1728,c_2516])).

tff(c_28,plain,(
    ! [A_24,B_25,C_26] :
      ( k2_relset_1(A_24,B_25,C_26) = k2_relat_1(C_26)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2587,plain,(
    ! [B_345,A_346,C_347] :
      ( k2_relset_1(B_345,A_346,k2_funct_1(C_347)) = k2_relat_1(k2_funct_1(C_347))
      | k2_relset_1(A_346,B_345,C_347) != B_345
      | ~ v2_funct_1(C_347)
      | ~ m1_subset_1(C_347,k1_zfmisc_1(k2_zfmisc_1(A_346,B_345)))
      | ~ v1_funct_2(C_347,A_346,B_345)
      | ~ v1_funct_1(C_347) ) ),
    inference(resolution,[status(thm)],[c_2417,c_28])).

tff(c_2593,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1632,c_2587])).

tff(c_2597,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1634,c_52,c_1633,c_2522,c_2593])).

tff(c_2599,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2267,c_2597])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 21:00:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.83/1.95  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.20/1.99  
% 5.20/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.20/1.99  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 5.20/1.99  
% 5.20/1.99  %Foreground sorts:
% 5.20/1.99  
% 5.20/1.99  
% 5.20/1.99  %Background operators:
% 5.20/1.99  
% 5.20/1.99  
% 5.20/1.99  %Foreground operators:
% 5.20/1.99  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.20/1.99  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.20/1.99  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.20/1.99  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.20/1.99  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.20/1.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.20/1.99  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.20/1.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.20/1.99  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.20/1.99  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 5.20/1.99  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.20/1.99  tff('#skF_2', type, '#skF_2': $i).
% 5.20/1.99  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.20/1.99  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.20/1.99  tff('#skF_3', type, '#skF_3': $i).
% 5.20/1.99  tff('#skF_1', type, '#skF_1': $i).
% 5.20/1.99  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.20/1.99  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.20/1.99  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.20/1.99  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.20/1.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.20/1.99  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.20/1.99  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.20/1.99  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.20/1.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.20/1.99  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.20/1.99  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.20/1.99  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 5.20/1.99  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.20/1.99  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.20/1.99  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.20/1.99  
% 5.20/2.03  tff(f_173, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_2)).
% 5.20/2.03  tff(f_129, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 5.20/2.03  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.20/2.03  tff(f_137, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_struct_0)).
% 5.20/2.03  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.20/2.03  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.20/2.03  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.20/2.03  tff(f_109, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 5.20/2.03  tff(f_101, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 5.20/2.03  tff(f_149, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 5.20/2.03  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.20/2.03  tff(f_54, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 5.20/2.03  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 5.20/2.03  tff(f_73, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v2_funct_1(A) & r1_tarski(B, k1_relat_1(A))) => (k9_relat_1(k2_funct_1(A), k9_relat_1(A, B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t177_funct_1)).
% 5.20/2.03  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 5.20/2.03  tff(f_125, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 5.20/2.03  tff(f_62, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k9_relat_1(B, A) = k10_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t154_funct_1)).
% 5.20/2.03  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.20/2.03  tff(c_60, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_173])).
% 5.20/2.03  tff(c_64, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_173])).
% 5.20/2.03  tff(c_62, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_173])).
% 5.20/2.03  tff(c_66, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_173])).
% 5.20/2.03  tff(c_70, plain, (![A_48]: (u1_struct_0(A_48)=k2_struct_0(A_48) | ~l1_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.20/2.03  tff(c_78, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_66, c_70])).
% 5.20/2.03  tff(c_77, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_62, c_70])).
% 5.20/2.03  tff(c_56, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_173])).
% 5.20/2.03  tff(c_102, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_77, c_56])).
% 5.20/2.03  tff(c_1440, plain, (![A_222, B_223, C_224]: (k2_relset_1(A_222, B_223, C_224)=k2_relat_1(C_224) | ~m1_subset_1(C_224, k1_zfmisc_1(k2_zfmisc_1(A_222, B_223))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.20/2.03  tff(c_1444, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_102, c_1440])).
% 5.20/2.03  tff(c_54, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_173])).
% 5.20/2.03  tff(c_97, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_77, c_54])).
% 5.20/2.03  tff(c_1445, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1444, c_97])).
% 5.20/2.03  tff(c_46, plain, (![A_37]: (~v1_xboole_0(k2_struct_0(A_37)) | ~l1_struct_0(A_37) | v2_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.20/2.03  tff(c_1460, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1445, c_46])).
% 5.20/2.03  tff(c_1464, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1460])).
% 5.20/2.03  tff(c_1465, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_64, c_1464])).
% 5.20/2.03  tff(c_10, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.20/2.03  tff(c_112, plain, (![B_53, A_54]: (v1_relat_1(B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(A_54)) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.20/2.03  tff(c_115, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_102, c_112])).
% 5.20/2.03  tff(c_118, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_115])).
% 5.20/2.03  tff(c_1380, plain, (![C_206, A_207, B_208]: (v4_relat_1(C_206, A_207) | ~m1_subset_1(C_206, k1_zfmisc_1(k2_zfmisc_1(A_207, B_208))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.20/2.03  tff(c_1384, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_102, c_1380])).
% 5.20/2.03  tff(c_1423, plain, (![B_217, A_218]: (k1_relat_1(B_217)=A_218 | ~v1_partfun1(B_217, A_218) | ~v4_relat_1(B_217, A_218) | ~v1_relat_1(B_217))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.20/2.03  tff(c_1426, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1384, c_1423])).
% 5.20/2.03  tff(c_1429, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_1426])).
% 5.20/2.03  tff(c_1430, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_1429])).
% 5.20/2.03  tff(c_58, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_173])).
% 5.20/2.03  tff(c_83, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_58])).
% 5.20/2.03  tff(c_84, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_83])).
% 5.20/2.03  tff(c_1455, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1445, c_84])).
% 5.20/2.03  tff(c_1454, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_1445, c_102])).
% 5.20/2.03  tff(c_1527, plain, (![C_227, A_228, B_229]: (v1_partfun1(C_227, A_228) | ~v1_funct_2(C_227, A_228, B_229) | ~v1_funct_1(C_227) | ~m1_subset_1(C_227, k1_zfmisc_1(k2_zfmisc_1(A_228, B_229))) | v1_xboole_0(B_229))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.20/2.03  tff(c_1530, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_1454, c_1527])).
% 5.20/2.03  tff(c_1533, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1455, c_1530])).
% 5.20/2.03  tff(c_1535, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1465, c_1430, c_1533])).
% 5.20/2.03  tff(c_1536, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_1429])).
% 5.20/2.03  tff(c_1538, plain, (![A_230, B_231, C_232]: (k2_relset_1(A_230, B_231, C_232)=k2_relat_1(C_232) | ~m1_subset_1(C_232, k1_zfmisc_1(k2_zfmisc_1(A_230, B_231))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.20/2.03  tff(c_1542, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_102, c_1538])).
% 5.20/2.03  tff(c_1601, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1536, c_1542])).
% 5.20/2.03  tff(c_1548, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1536, c_97])).
% 5.20/2.03  tff(c_1631, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1601, c_1548])).
% 5.20/2.03  tff(c_1549, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1536, c_84])).
% 5.20/2.03  tff(c_1634, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1631, c_1549])).
% 5.20/2.03  tff(c_1633, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1631, c_1601])).
% 5.20/2.03  tff(c_52, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_173])).
% 5.20/2.03  tff(c_1547, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_1536, c_102])).
% 5.20/2.03  tff(c_1632, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_1631, c_1547])).
% 5.20/2.03  tff(c_2260, plain, (![A_309, B_310, C_311]: (k2_tops_2(A_309, B_310, C_311)=k2_funct_1(C_311) | ~v2_funct_1(C_311) | k2_relset_1(A_309, B_310, C_311)!=B_310 | ~m1_subset_1(C_311, k1_zfmisc_1(k2_zfmisc_1(A_309, B_310))) | ~v1_funct_2(C_311, A_309, B_310) | ~v1_funct_1(C_311))), inference(cnfTransformation, [status(thm)], [f_149])).
% 5.20/2.03  tff(c_2263, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1632, c_2260])).
% 5.20/2.03  tff(c_2266, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1634, c_1633, c_52, c_2263])).
% 5.20/2.03  tff(c_181, plain, (![A_71, B_72, C_73]: (k2_relset_1(A_71, B_72, C_73)=k2_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.20/2.03  tff(c_185, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_102, c_181])).
% 5.20/2.03  tff(c_186, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_185, c_97])).
% 5.20/2.03  tff(c_201, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_186, c_46])).
% 5.20/2.03  tff(c_205, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_201])).
% 5.20/2.03  tff(c_206, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_64, c_205])).
% 5.20/2.03  tff(c_121, plain, (![C_55, A_56, B_57]: (v4_relat_1(C_55, A_56) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.20/2.03  tff(c_125, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_102, c_121])).
% 5.20/2.03  tff(c_164, plain, (![B_66, A_67]: (k1_relat_1(B_66)=A_67 | ~v1_partfun1(B_66, A_67) | ~v4_relat_1(B_66, A_67) | ~v1_relat_1(B_66))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.20/2.03  tff(c_167, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_125, c_164])).
% 5.20/2.03  tff(c_170, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_167])).
% 5.20/2.03  tff(c_171, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_170])).
% 5.20/2.03  tff(c_196, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_186, c_84])).
% 5.20/2.03  tff(c_195, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_186, c_102])).
% 5.20/2.03  tff(c_263, plain, (![C_76, A_77, B_78]: (v1_partfun1(C_76, A_77) | ~v1_funct_2(C_76, A_77, B_78) | ~v1_funct_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))) | v1_xboole_0(B_78))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.20/2.03  tff(c_266, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_195, c_263])).
% 5.20/2.03  tff(c_269, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_196, c_266])).
% 5.20/2.03  tff(c_271, plain, $false, inference(negUnitSimplification, [status(thm)], [c_206, c_171, c_269])).
% 5.20/2.03  tff(c_272, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_170])).
% 5.20/2.03  tff(c_278, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_272, c_102])).
% 5.20/2.03  tff(c_360, plain, (![A_82, B_83, C_84]: (k2_relset_1(A_82, B_83, C_84)=k2_relat_1(C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.20/2.03  tff(c_364, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_278, c_360])).
% 5.20/2.03  tff(c_279, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_272, c_97])).
% 5.20/2.03  tff(c_365, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_364, c_279])).
% 5.20/2.03  tff(c_280, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_272, c_84])).
% 5.20/2.03  tff(c_372, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_365, c_280])).
% 5.20/2.03  tff(c_370, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_365, c_364])).
% 5.20/2.03  tff(c_373, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_365, c_278])).
% 5.20/2.03  tff(c_1280, plain, (![A_188, B_189, C_190]: (k2_tops_2(A_188, B_189, C_190)=k2_funct_1(C_190) | ~v2_funct_1(C_190) | k2_relset_1(A_188, B_189, C_190)!=B_189 | ~m1_subset_1(C_190, k1_zfmisc_1(k2_zfmisc_1(A_188, B_189))) | ~v1_funct_2(C_190, A_188, B_189) | ~v1_funct_1(C_190))), inference(cnfTransformation, [status(thm)], [f_149])).
% 5.20/2.03  tff(c_1283, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_373, c_1280])).
% 5.20/2.03  tff(c_1286, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_372, c_370, c_52, c_1283])).
% 5.20/2.03  tff(c_50, plain, (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_173])).
% 5.20/2.03  tff(c_119, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_78, c_77, c_77, c_78, c_78, c_77, c_77, c_50])).
% 5.20/2.03  tff(c_120, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_119])).
% 5.20/2.03  tff(c_274, plain, (k1_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_272, c_272, c_120])).
% 5.20/2.03  tff(c_441, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_365, c_365, c_365, c_274])).
% 5.20/2.03  tff(c_1288, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1286, c_441])).
% 5.20/2.03  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.20/2.03  tff(c_138, plain, (![B_60, A_61]: (k7_relat_1(B_60, A_61)=B_60 | ~v4_relat_1(B_60, A_61) | ~v1_relat_1(B_60))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.20/2.03  tff(c_141, plain, (k7_relat_1('#skF_3', k2_struct_0('#skF_1'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_125, c_138])).
% 5.20/2.03  tff(c_144, plain, (k7_relat_1('#skF_3', k2_struct_0('#skF_1'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_118, c_141])).
% 5.20/2.03  tff(c_276, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_272, c_144])).
% 5.20/2.03  tff(c_12, plain, (![B_9, A_8]: (k2_relat_1(k7_relat_1(B_9, A_8))=k9_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.20/2.03  tff(c_318, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_276, c_12])).
% 5.20/2.03  tff(c_322, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_318])).
% 5.20/2.03  tff(c_450, plain, (![A_90, B_91]: (k9_relat_1(k2_funct_1(A_90), k9_relat_1(A_90, B_91))=B_91 | ~r1_tarski(B_91, k1_relat_1(A_90)) | ~v2_funct_1(A_90) | ~v1_funct_1(A_90) | ~v1_relat_1(A_90))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.20/2.03  tff(c_465, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k1_relat_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_322, c_450])).
% 5.20/2.03  tff(c_469, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_60, c_52, c_6, c_465])).
% 5.20/2.03  tff(c_126, plain, (![B_58, A_59]: (k2_relat_1(k7_relat_1(B_58, A_59))=k9_relat_1(B_58, A_59) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.20/2.03  tff(c_14, plain, (![A_10]: (k10_relat_1(A_10, k2_relat_1(A_10))=k1_relat_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.20/2.03  tff(c_489, plain, (![B_93, A_94]: (k10_relat_1(k7_relat_1(B_93, A_94), k9_relat_1(B_93, A_94))=k1_relat_1(k7_relat_1(B_93, A_94)) | ~v1_relat_1(k7_relat_1(B_93, A_94)) | ~v1_relat_1(B_93))), inference(superposition, [status(thm), theory('equality')], [c_126, c_14])).
% 5.20/2.03  tff(c_501, plain, (k10_relat_1(k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')), k1_relat_1('#skF_3'))=k1_relat_1(k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))) | ~v1_relat_1(k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_469, c_489])).
% 5.20/2.03  tff(c_541, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_501])).
% 5.20/2.03  tff(c_558, plain, (![C_104, B_105, A_106]: (m1_subset_1(k2_funct_1(C_104), k1_zfmisc_1(k2_zfmisc_1(B_105, A_106))) | k2_relset_1(A_106, B_105, C_104)!=B_105 | ~v2_funct_1(C_104) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_106, B_105))) | ~v1_funct_2(C_104, A_106, B_105) | ~v1_funct_1(C_104))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.20/2.03  tff(c_8, plain, (![B_5, A_3]: (v1_relat_1(B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_3)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.20/2.03  tff(c_585, plain, (![C_104, B_105, A_106]: (v1_relat_1(k2_funct_1(C_104)) | ~v1_relat_1(k2_zfmisc_1(B_105, A_106)) | k2_relset_1(A_106, B_105, C_104)!=B_105 | ~v2_funct_1(C_104) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_106, B_105))) | ~v1_funct_2(C_104, A_106, B_105) | ~v1_funct_1(C_104))), inference(resolution, [status(thm)], [c_558, c_8])).
% 5.20/2.03  tff(c_602, plain, (![C_107, A_108, B_109]: (v1_relat_1(k2_funct_1(C_107)) | k2_relset_1(A_108, B_109, C_107)!=B_109 | ~v2_funct_1(C_107) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))) | ~v1_funct_2(C_107, A_108, B_109) | ~v1_funct_1(C_107))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_585])).
% 5.20/2.03  tff(c_608, plain, (v1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_373, c_602])).
% 5.20/2.03  tff(c_612, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_372, c_52, c_370, c_608])).
% 5.20/2.03  tff(c_614, plain, $false, inference(negUnitSimplification, [status(thm)], [c_541, c_612])).
% 5.20/2.03  tff(c_616, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_501])).
% 5.20/2.03  tff(c_994, plain, (![C_161, B_162, A_163]: (m1_subset_1(k2_funct_1(C_161), k1_zfmisc_1(k2_zfmisc_1(B_162, A_163))) | k2_relset_1(A_163, B_162, C_161)!=B_162 | ~v2_funct_1(C_161) | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(A_163, B_162))) | ~v1_funct_2(C_161, A_163, B_162) | ~v1_funct_1(C_161))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.20/2.03  tff(c_24, plain, (![C_20, A_18, B_19]: (v4_relat_1(C_20, A_18) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.20/2.03  tff(c_1055, plain, (![C_170, B_171, A_172]: (v4_relat_1(k2_funct_1(C_170), B_171) | k2_relset_1(A_172, B_171, C_170)!=B_171 | ~v2_funct_1(C_170) | ~m1_subset_1(C_170, k1_zfmisc_1(k2_zfmisc_1(A_172, B_171))) | ~v1_funct_2(C_170, A_172, B_171) | ~v1_funct_1(C_170))), inference(resolution, [status(thm)], [c_994, c_24])).
% 5.20/2.03  tff(c_1061, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_373, c_1055])).
% 5.20/2.03  tff(c_1065, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_372, c_52, c_370, c_1061])).
% 5.20/2.03  tff(c_16, plain, (![B_12, A_11]: (k7_relat_1(B_12, A_11)=B_12 | ~v4_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.20/2.03  tff(c_1071, plain, (k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1065, c_16])).
% 5.20/2.03  tff(c_1077, plain, (k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_616, c_1071])).
% 5.20/2.03  tff(c_1087, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1077, c_12])).
% 5.20/2.03  tff(c_1093, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_616, c_469, c_1087])).
% 5.20/2.03  tff(c_422, plain, (![B_85, A_86]: (k10_relat_1(k2_funct_1(B_85), A_86)=k9_relat_1(B_85, A_86) | ~v2_funct_1(B_85) | ~v1_funct_1(B_85) | ~v1_relat_1(B_85))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.20/2.03  tff(c_436, plain, (![B_85]: (k9_relat_1(B_85, k2_relat_1(k2_funct_1(B_85)))=k1_relat_1(k2_funct_1(B_85)) | ~v2_funct_1(B_85) | ~v1_funct_1(B_85) | ~v1_relat_1(B_85) | ~v1_relat_1(k2_funct_1(B_85)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_422])).
% 5.20/2.03  tff(c_1109, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1093, c_436])).
% 5.20/2.03  tff(c_1116, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_616, c_118, c_60, c_52, c_322, c_1109])).
% 5.20/2.03  tff(c_752, plain, (![C_131, B_132, A_133]: (m1_subset_1(k2_funct_1(C_131), k1_zfmisc_1(k2_zfmisc_1(B_132, A_133))) | k2_relset_1(A_133, B_132, C_131)!=B_132 | ~v2_funct_1(C_131) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_133, B_132))) | ~v1_funct_2(C_131, A_133, B_132) | ~v1_funct_1(C_131))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.20/2.03  tff(c_813, plain, (![C_140, B_141, A_142]: (v4_relat_1(k2_funct_1(C_140), B_141) | k2_relset_1(A_142, B_141, C_140)!=B_141 | ~v2_funct_1(C_140) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_142, B_141))) | ~v1_funct_2(C_140, A_142, B_141) | ~v1_funct_1(C_140))), inference(resolution, [status(thm)], [c_752, c_24])).
% 5.20/2.03  tff(c_819, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_373, c_813])).
% 5.20/2.03  tff(c_823, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_372, c_52, c_370, c_819])).
% 5.20/2.03  tff(c_829, plain, (k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_823, c_16])).
% 5.20/2.03  tff(c_835, plain, (k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_616, c_829])).
% 5.20/2.03  tff(c_845, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_835, c_12])).
% 5.20/2.03  tff(c_851, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_616, c_469, c_845])).
% 5.20/2.03  tff(c_856, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_851, c_436])).
% 5.20/2.03  tff(c_863, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_616, c_118, c_60, c_52, c_322, c_856])).
% 5.20/2.03  tff(c_533, plain, (![C_95, A_96, B_97]: (v1_funct_1(k2_funct_1(C_95)) | k2_relset_1(A_96, B_97, C_95)!=B_97 | ~v2_funct_1(C_95) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))) | ~v1_funct_2(C_95, A_96, B_97) | ~v1_funct_1(C_95))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.20/2.03  tff(c_536, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_373, c_533])).
% 5.20/2.03  tff(c_539, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_372, c_52, c_370, c_536])).
% 5.20/2.03  tff(c_20, plain, (![A_15, B_17]: (k9_relat_1(k2_funct_1(A_15), k9_relat_1(A_15, B_17))=B_17 | ~r1_tarski(B_17, k1_relat_1(A_15)) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.20/2.03  tff(c_473, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~r1_tarski(k2_relat_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_469, c_20])).
% 5.20/2.03  tff(c_618, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~r1_tarski(k2_relat_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_539, c_473])).
% 5.20/2.03  tff(c_619, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_618])).
% 5.20/2.03  tff(c_621, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_616, c_619])).
% 5.20/2.03  tff(c_622, plain, (~v2_funct_1(k2_funct_1('#skF_3')) | ~r1_tarski(k2_relat_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3'))) | k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_618])).
% 5.20/2.03  tff(c_625, plain, (~r1_tarski(k2_relat_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_622])).
% 5.20/2.03  tff(c_867, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_863, c_625])).
% 5.20/2.03  tff(c_870, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_867])).
% 5.20/2.03  tff(c_872, plain, (r1_tarski(k2_relat_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_622])).
% 5.20/2.03  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.20/2.03  tff(c_875, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_872, c_2])).
% 5.20/2.03  tff(c_977, plain, (~r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), k2_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_875])).
% 5.20/2.03  tff(c_1120, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1116, c_977])).
% 5.20/2.03  tff(c_1124, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1120])).
% 5.20/2.03  tff(c_1125, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_875])).
% 5.20/2.03  tff(c_1293, plain, (![C_191, B_192, A_193]: (m1_subset_1(k2_funct_1(C_191), k1_zfmisc_1(k2_zfmisc_1(B_192, A_193))) | k2_relset_1(A_193, B_192, C_191)!=B_192 | ~v2_funct_1(C_191) | ~m1_subset_1(C_191, k1_zfmisc_1(k2_zfmisc_1(A_193, B_192))) | ~v1_funct_2(C_191, A_193, B_192) | ~v1_funct_1(C_191))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.20/2.03  tff(c_26, plain, (![A_21, B_22, C_23]: (k1_relset_1(A_21, B_22, C_23)=k1_relat_1(C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.20/2.03  tff(c_1365, plain, (![B_203, A_204, C_205]: (k1_relset_1(B_203, A_204, k2_funct_1(C_205))=k1_relat_1(k2_funct_1(C_205)) | k2_relset_1(A_204, B_203, C_205)!=B_203 | ~v2_funct_1(C_205) | ~m1_subset_1(C_205, k1_zfmisc_1(k2_zfmisc_1(A_204, B_203))) | ~v1_funct_2(C_205, A_204, B_203) | ~v1_funct_1(C_205))), inference(resolution, [status(thm)], [c_1293, c_26])).
% 5.20/2.03  tff(c_1371, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_373, c_1365])).
% 5.20/2.03  tff(c_1375, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_372, c_52, c_370, c_1125, c_1371])).
% 5.20/2.03  tff(c_1377, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1288, c_1375])).
% 5.20/2.03  tff(c_1378, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_119])).
% 5.20/2.03  tff(c_1545, plain, (k2_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1536, c_1536, c_1536, c_1378])).
% 5.20/2.03  tff(c_1708, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1631, c_1631, c_1545])).
% 5.20/2.03  tff(c_2267, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2266, c_1708])).
% 5.20/2.03  tff(c_1744, plain, (![C_243, A_244, B_245]: (v1_funct_1(k2_funct_1(C_243)) | k2_relset_1(A_244, B_245, C_243)!=B_245 | ~v2_funct_1(C_243) | ~m1_subset_1(C_243, k1_zfmisc_1(k2_zfmisc_1(A_244, B_245))) | ~v1_funct_2(C_243, A_244, B_245) | ~v1_funct_1(C_243))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.20/2.03  tff(c_1747, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1632, c_1744])).
% 5.20/2.03  tff(c_1750, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1634, c_52, c_1633, c_1747])).
% 5.20/2.03  tff(c_1402, plain, (![B_214, A_215]: (k7_relat_1(B_214, A_215)=B_214 | ~v4_relat_1(B_214, A_215) | ~v1_relat_1(B_214))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.20/2.03  tff(c_1405, plain, (k7_relat_1('#skF_3', k2_struct_0('#skF_1'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1384, c_1402])).
% 5.20/2.03  tff(c_1408, plain, (k7_relat_1('#skF_3', k2_struct_0('#skF_1'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_118, c_1405])).
% 5.20/2.03  tff(c_1544, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1536, c_1408])).
% 5.20/2.03  tff(c_1587, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1544, c_12])).
% 5.20/2.03  tff(c_1591, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_1587])).
% 5.20/2.03  tff(c_1709, plain, (![A_238, B_239]: (k9_relat_1(k2_funct_1(A_238), k9_relat_1(A_238, B_239))=B_239 | ~r1_tarski(B_239, k1_relat_1(A_238)) | ~v2_funct_1(A_238) | ~v1_funct_1(A_238) | ~v1_relat_1(A_238))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.20/2.03  tff(c_1724, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k1_relat_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1591, c_1709])).
% 5.20/2.03  tff(c_1728, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_60, c_52, c_6, c_1724])).
% 5.20/2.03  tff(c_1732, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~r1_tarski(k2_relat_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1728, c_20])).
% 5.20/2.03  tff(c_1809, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~r1_tarski(k2_relat_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1750, c_1732])).
% 5.20/2.03  tff(c_1810, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1809])).
% 5.20/2.03  tff(c_1835, plain, (![C_255, B_256, A_257]: (m1_subset_1(k2_funct_1(C_255), k1_zfmisc_1(k2_zfmisc_1(B_256, A_257))) | k2_relset_1(A_257, B_256, C_255)!=B_256 | ~v2_funct_1(C_255) | ~m1_subset_1(C_255, k1_zfmisc_1(k2_zfmisc_1(A_257, B_256))) | ~v1_funct_2(C_255, A_257, B_256) | ~v1_funct_1(C_255))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.20/2.03  tff(c_1862, plain, (![C_255, B_256, A_257]: (v1_relat_1(k2_funct_1(C_255)) | ~v1_relat_1(k2_zfmisc_1(B_256, A_257)) | k2_relset_1(A_257, B_256, C_255)!=B_256 | ~v2_funct_1(C_255) | ~m1_subset_1(C_255, k1_zfmisc_1(k2_zfmisc_1(A_257, B_256))) | ~v1_funct_2(C_255, A_257, B_256) | ~v1_funct_1(C_255))), inference(resolution, [status(thm)], [c_1835, c_8])).
% 5.20/2.03  tff(c_1874, plain, (![C_258, A_259, B_260]: (v1_relat_1(k2_funct_1(C_258)) | k2_relset_1(A_259, B_260, C_258)!=B_260 | ~v2_funct_1(C_258) | ~m1_subset_1(C_258, k1_zfmisc_1(k2_zfmisc_1(A_259, B_260))) | ~v1_funct_2(C_258, A_259, B_260) | ~v1_funct_1(C_258))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1862])).
% 5.20/2.03  tff(c_1880, plain, (v1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1632, c_1874])).
% 5.20/2.03  tff(c_1884, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1634, c_52, c_1633, c_1880])).
% 5.20/2.03  tff(c_1886, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1810, c_1884])).
% 5.20/2.03  tff(c_1888, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1809])).
% 5.20/2.03  tff(c_2282, plain, (![C_312, B_313, A_314]: (m1_subset_1(k2_funct_1(C_312), k1_zfmisc_1(k2_zfmisc_1(B_313, A_314))) | k2_relset_1(A_314, B_313, C_312)!=B_313 | ~v2_funct_1(C_312) | ~m1_subset_1(C_312, k1_zfmisc_1(k2_zfmisc_1(A_314, B_313))) | ~v1_funct_2(C_312, A_314, B_313) | ~v1_funct_1(C_312))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.20/2.03  tff(c_2343, plain, (![C_321, B_322, A_323]: (v4_relat_1(k2_funct_1(C_321), B_322) | k2_relset_1(A_323, B_322, C_321)!=B_322 | ~v2_funct_1(C_321) | ~m1_subset_1(C_321, k1_zfmisc_1(k2_zfmisc_1(A_323, B_322))) | ~v1_funct_2(C_321, A_323, B_322) | ~v1_funct_1(C_321))), inference(resolution, [status(thm)], [c_2282, c_24])).
% 5.20/2.03  tff(c_2349, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1632, c_2343])).
% 5.20/2.03  tff(c_2353, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1634, c_52, c_1633, c_2349])).
% 5.20/2.03  tff(c_2359, plain, (k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2353, c_16])).
% 5.20/2.03  tff(c_2365, plain, (k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1888, c_2359])).
% 5.20/2.03  tff(c_2375, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2365, c_12])).
% 5.20/2.03  tff(c_2381, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1888, c_1728, c_2375])).
% 5.20/2.03  tff(c_1651, plain, (![B_236, A_237]: (k10_relat_1(k2_funct_1(B_236), A_237)=k9_relat_1(B_236, A_237) | ~v2_funct_1(B_236) | ~v1_funct_1(B_236) | ~v1_relat_1(B_236))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.20/2.03  tff(c_1665, plain, (![B_236]: (k9_relat_1(B_236, k2_relat_1(k2_funct_1(B_236)))=k1_relat_1(k2_funct_1(B_236)) | ~v2_funct_1(B_236) | ~v1_funct_1(B_236) | ~v1_relat_1(B_236) | ~v1_relat_1(k2_funct_1(B_236)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1651])).
% 5.20/2.03  tff(c_2387, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2381, c_1665])).
% 5.20/2.03  tff(c_2394, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1888, c_118, c_60, c_52, c_1591, c_2387])).
% 5.20/2.03  tff(c_2017, plain, (![C_279, B_280, A_281]: (m1_subset_1(k2_funct_1(C_279), k1_zfmisc_1(k2_zfmisc_1(B_280, A_281))) | k2_relset_1(A_281, B_280, C_279)!=B_280 | ~v2_funct_1(C_279) | ~m1_subset_1(C_279, k1_zfmisc_1(k2_zfmisc_1(A_281, B_280))) | ~v1_funct_2(C_279, A_281, B_280) | ~v1_funct_1(C_279))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.20/2.03  tff(c_2078, plain, (![C_288, B_289, A_290]: (v4_relat_1(k2_funct_1(C_288), B_289) | k2_relset_1(A_290, B_289, C_288)!=B_289 | ~v2_funct_1(C_288) | ~m1_subset_1(C_288, k1_zfmisc_1(k2_zfmisc_1(A_290, B_289))) | ~v1_funct_2(C_288, A_290, B_289) | ~v1_funct_1(C_288))), inference(resolution, [status(thm)], [c_2017, c_24])).
% 5.20/2.03  tff(c_2084, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1632, c_2078])).
% 5.20/2.03  tff(c_2088, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1634, c_52, c_1633, c_2084])).
% 5.20/2.03  tff(c_2094, plain, (k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2088, c_16])).
% 5.20/2.03  tff(c_2100, plain, (k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1888, c_2094])).
% 5.20/2.03  tff(c_2110, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2100, c_12])).
% 5.20/2.03  tff(c_2116, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1888, c_1728, c_2110])).
% 5.20/2.03  tff(c_2121, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2116, c_1665])).
% 5.20/2.03  tff(c_2128, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1888, c_118, c_60, c_52, c_1591, c_2121])).
% 5.20/2.03  tff(c_1887, plain, (~v2_funct_1(k2_funct_1('#skF_3')) | ~r1_tarski(k2_relat_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3'))) | k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_1809])).
% 5.20/2.03  tff(c_1889, plain, (~r1_tarski(k2_relat_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_1887])).
% 5.20/2.03  tff(c_2132, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2128, c_1889])).
% 5.20/2.03  tff(c_2135, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_2132])).
% 5.20/2.03  tff(c_2137, plain, (r1_tarski(k2_relat_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_1887])).
% 5.20/2.03  tff(c_2140, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_2137, c_2])).
% 5.20/2.03  tff(c_2281, plain, (~r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), k2_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_2140])).
% 5.20/2.03  tff(c_2398, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2394, c_2281])).
% 5.20/2.03  tff(c_2402, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_2398])).
% 5.20/2.03  tff(c_2403, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_2140])).
% 5.20/2.03  tff(c_34, plain, (![B_32]: (v1_partfun1(B_32, k1_relat_1(B_32)) | ~v4_relat_1(B_32, k1_relat_1(B_32)) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.20/2.03  tff(c_2410, plain, (v1_partfun1(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3'))) | ~v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2403, c_34])).
% 5.20/2.03  tff(c_2414, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1888, c_2403, c_2410])).
% 5.20/2.03  tff(c_2456, plain, (~v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_2414])).
% 5.20/2.03  tff(c_2417, plain, (![C_324, B_325, A_326]: (m1_subset_1(k2_funct_1(C_324), k1_zfmisc_1(k2_zfmisc_1(B_325, A_326))) | k2_relset_1(A_326, B_325, C_324)!=B_325 | ~v2_funct_1(C_324) | ~m1_subset_1(C_324, k1_zfmisc_1(k2_zfmisc_1(A_326, B_325))) | ~v1_funct_2(C_324, A_326, B_325) | ~v1_funct_1(C_324))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.20/2.03  tff(c_2479, plain, (![C_333, B_334, A_335]: (v4_relat_1(k2_funct_1(C_333), B_334) | k2_relset_1(A_335, B_334, C_333)!=B_334 | ~v2_funct_1(C_333) | ~m1_subset_1(C_333, k1_zfmisc_1(k2_zfmisc_1(A_335, B_334))) | ~v1_funct_2(C_333, A_335, B_334) | ~v1_funct_1(C_333))), inference(resolution, [status(thm)], [c_2417, c_24])).
% 5.20/2.03  tff(c_2485, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1632, c_2479])).
% 5.20/2.03  tff(c_2489, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1634, c_52, c_1633, c_2485])).
% 5.20/2.03  tff(c_2491, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2456, c_2489])).
% 5.20/2.03  tff(c_2493, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_2414])).
% 5.20/2.03  tff(c_2499, plain, (k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2493, c_16])).
% 5.20/2.03  tff(c_2505, plain, (k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1888, c_2499])).
% 5.20/2.03  tff(c_2516, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2505, c_12])).
% 5.20/2.03  tff(c_2522, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1888, c_1728, c_2516])).
% 5.20/2.03  tff(c_28, plain, (![A_24, B_25, C_26]: (k2_relset_1(A_24, B_25, C_26)=k2_relat_1(C_26) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.20/2.03  tff(c_2587, plain, (![B_345, A_346, C_347]: (k2_relset_1(B_345, A_346, k2_funct_1(C_347))=k2_relat_1(k2_funct_1(C_347)) | k2_relset_1(A_346, B_345, C_347)!=B_345 | ~v2_funct_1(C_347) | ~m1_subset_1(C_347, k1_zfmisc_1(k2_zfmisc_1(A_346, B_345))) | ~v1_funct_2(C_347, A_346, B_345) | ~v1_funct_1(C_347))), inference(resolution, [status(thm)], [c_2417, c_28])).
% 5.20/2.03  tff(c_2593, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1632, c_2587])).
% 5.20/2.03  tff(c_2597, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1634, c_52, c_1633, c_2522, c_2593])).
% 5.20/2.03  tff(c_2599, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2267, c_2597])).
% 5.20/2.03  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.20/2.03  
% 5.20/2.03  Inference rules
% 5.20/2.03  ----------------------
% 5.20/2.03  #Ref     : 0
% 5.20/2.03  #Sup     : 558
% 5.20/2.03  #Fact    : 0
% 5.20/2.03  #Define  : 0
% 5.20/2.03  #Split   : 23
% 5.20/2.03  #Chain   : 0
% 5.20/2.03  #Close   : 0
% 5.20/2.03  
% 5.20/2.03  Ordering : KBO
% 5.20/2.03  
% 5.20/2.03  Simplification rules
% 5.20/2.03  ----------------------
% 5.20/2.03  #Subsume      : 4
% 5.20/2.03  #Demod        : 659
% 5.20/2.03  #Tautology    : 275
% 5.20/2.03  #SimpNegUnit  : 14
% 5.20/2.03  #BackRed      : 86
% 5.20/2.03  
% 5.20/2.03  #Partial instantiations: 0
% 5.20/2.03  #Strategies tried      : 1
% 5.20/2.03  
% 5.20/2.03  Timing (in seconds)
% 5.20/2.03  ----------------------
% 5.20/2.04  Preprocessing        : 0.44
% 5.20/2.04  Parsing              : 0.25
% 5.20/2.04  CNF conversion       : 0.03
% 5.20/2.04  Main loop            : 0.77
% 5.20/2.04  Inferencing          : 0.28
% 5.20/2.04  Reduction            : 0.26
% 5.20/2.04  Demodulation         : 0.18
% 5.20/2.04  BG Simplification    : 0.04
% 5.20/2.04  Subsumption          : 0.13
% 5.20/2.04  Abstraction          : 0.04
% 5.20/2.04  MUC search           : 0.00
% 5.20/2.04  Cooper               : 0.00
% 5.20/2.04  Total                : 1.30
% 5.20/2.04  Index Insertion      : 0.00
% 5.20/2.04  Index Deletion       : 0.00
% 5.20/2.04  Index Matching       : 0.00
% 5.20/2.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
