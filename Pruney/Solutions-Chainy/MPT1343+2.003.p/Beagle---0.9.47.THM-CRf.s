%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:47 EST 2020

% Result     : Theorem 8.28s
% Output     : CNFRefutation 8.67s
% Verified   : 
% Statistics : Number of formulae       :  237 (5185 expanded)
%              Number of leaves         :   76 (1837 expanded)
%              Depth                    :   26
%              Number of atoms          :  383 (14501 expanded)
%              Number of equality atoms :  125 (3708 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v5_ordinal1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k8_relset_1 > k7_relset_1 > k2_enumset1 > k2_tops_2 > k2_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > u1_struct_0 > k4_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v5_ordinal1,type,(
    v5_ordinal1: $i > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_102,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_255,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( l1_struct_0(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                   => ( ( k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                        & v2_funct_1(C) )
                     => k7_relset_1(u1_struct_0(A),u1_struct_0(B),C,D) = k8_relset_1(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C),D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tops_2)).

tff(f_221,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_94,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_156,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k9_relat_1(B,A) = k10_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).

tff(f_166,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_141,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_110,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_133,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_100,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ( v1_xboole_0(k4_relat_1(A))
        & v1_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_relat_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_180,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_200,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_184,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_217,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | v1_partfun1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

tff(f_81,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_174,axiom,(
    ! [A] :
      ( v1_relat_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,A)
      & v1_funct_1(k1_xboole_0)
      & v5_ordinal1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_ordinal1)).

tff(f_112,axiom,(
    ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(f_125,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_148,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k2_relat_1(B))
      <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_118,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_106,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_122,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_192,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_233,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_188,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_77,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_46,plain,(
    ! [A_49,B_50] : v1_relat_1(k2_zfmisc_1(A_49,B_50)) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_122,plain,(
    l1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_193,plain,(
    ! [A_112] :
      ( u1_struct_0(A_112) = k2_struct_0(A_112)
      | ~ l1_struct_0(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_200,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_122,c_193])).

tff(c_124,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_201,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_124,c_193])).

tff(c_116,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_999,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_201,c_116])).

tff(c_40,plain,(
    ! [B_47,A_45] :
      ( v1_relat_1(B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_45))
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1002,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_999,c_40])).

tff(c_1008,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1002])).

tff(c_120,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_110,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_72,plain,(
    ! [B_63,A_62] :
      ( k10_relat_1(k2_funct_1(B_63),A_62) = k9_relat_1(B_63,A_62)
      | ~ v2_funct_1(B_63)
      | ~ v1_funct_1(B_63)
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_74,plain,(
    ! [A_64] :
      ( k2_relat_1(k2_funct_1(A_64)) = k1_relat_1(A_64)
      | ~ v2_funct_1(A_64)
      | ~ v1_funct_1(A_64)
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_66,plain,(
    ! [A_59] :
      ( v1_relat_1(k2_funct_1(A_59))
      | ~ v1_funct_1(A_59)
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_1503,plain,(
    ! [A_288] :
      ( k2_relat_1(k2_funct_1(A_288)) = k1_relat_1(A_288)
      | ~ v2_funct_1(A_288)
      | ~ v1_funct_1(A_288)
      | ~ v1_relat_1(A_288) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_50,plain,(
    ! [A_53] :
      ( k10_relat_1(A_53,k2_relat_1(A_53)) = k1_relat_1(A_53)
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_4167,plain,(
    ! [A_623] :
      ( k10_relat_1(k2_funct_1(A_623),k1_relat_1(A_623)) = k1_relat_1(k2_funct_1(A_623))
      | ~ v1_relat_1(k2_funct_1(A_623))
      | ~ v2_funct_1(A_623)
      | ~ v1_funct_1(A_623)
      | ~ v1_relat_1(A_623) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1503,c_50])).

tff(c_7586,plain,(
    ! [A_873] :
      ( k9_relat_1(A_873,k1_relat_1(A_873)) = k1_relat_1(k2_funct_1(A_873))
      | ~ v2_funct_1(A_873)
      | ~ v1_funct_1(A_873)
      | ~ v1_relat_1(A_873)
      | ~ v1_relat_1(k2_funct_1(A_873))
      | ~ v2_funct_1(A_873)
      | ~ v1_funct_1(A_873)
      | ~ v1_relat_1(A_873) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4167,c_72])).

tff(c_7590,plain,(
    ! [A_874] :
      ( k9_relat_1(A_874,k1_relat_1(A_874)) = k1_relat_1(k2_funct_1(A_874))
      | ~ v2_funct_1(A_874)
      | ~ v1_funct_1(A_874)
      | ~ v1_relat_1(A_874) ) ),
    inference(resolution,[status(thm)],[c_66,c_7586])).

tff(c_1189,plain,(
    ! [A_250] :
      ( k4_relat_1(A_250) = k2_funct_1(A_250)
      | ~ v2_funct_1(A_250)
      | ~ v1_funct_1(A_250)
      | ~ v1_relat_1(A_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1192,plain,
    ( k4_relat_1('#skF_4') = k2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_110,c_1189])).

tff(c_1195,plain,(
    k4_relat_1('#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1008,c_120,c_1192])).

tff(c_44,plain,(
    ! [A_48] :
      ( v1_xboole_0(k4_relat_1(A_48))
      | ~ v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1202,plain,
    ( v1_xboole_0(k2_funct_1('#skF_4'))
    | ~ v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1195,c_44])).

tff(c_1209,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1202])).

tff(c_28,plain,(
    ! [A_37] : k2_zfmisc_1(A_37,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1074,plain,(
    ! [C_237,A_238,B_239] :
      ( v4_relat_1(C_237,A_238)
      | ~ m1_subset_1(C_237,k1_zfmisc_1(k2_zfmisc_1(A_238,B_239))) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_1092,plain,(
    v4_relat_1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_999,c_1074])).

tff(c_1386,plain,(
    ! [B_277,A_278] :
      ( k1_relat_1(B_277) = A_278
      | ~ v1_partfun1(B_277,A_278)
      | ~ v4_relat_1(B_277,A_278)
      | ~ v1_relat_1(B_277) ) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_1395,plain,
    ( k2_struct_0('#skF_2') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',k2_struct_0('#skF_2'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1092,c_1386])).

tff(c_1404,plain,
    ( k2_struct_0('#skF_2') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1008,c_1395])).

tff(c_1540,plain,(
    ~ v1_partfun1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1404])).

tff(c_1719,plain,(
    ! [A_316,B_317,C_318] :
      ( k2_relset_1(A_316,B_317,C_318) = k2_relat_1(C_318)
      | ~ m1_subset_1(C_318,k1_zfmisc_1(k2_zfmisc_1(A_316,B_317))) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_1737,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'),'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_999,c_1719])).

tff(c_112,plain,(
    k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4') = k2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_244,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'),'#skF_4') = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_200,c_112])).

tff(c_1748,plain,(
    k2_struct_0('#skF_3') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1737,c_244])).

tff(c_118,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_202,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_118])).

tff(c_221,plain,(
    v1_funct_2('#skF_4',k2_struct_0('#skF_2'),k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_202])).

tff(c_1759,plain,(
    v1_funct_2('#skF_4',k2_struct_0('#skF_2'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1748,c_221])).

tff(c_1758,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_relat_1('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1748,c_999])).

tff(c_2379,plain,(
    ! [B_416,C_417,A_418] :
      ( k1_xboole_0 = B_416
      | v1_partfun1(C_417,A_418)
      | ~ v1_funct_2(C_417,A_418,B_416)
      | ~ m1_subset_1(C_417,k1_zfmisc_1(k2_zfmisc_1(A_418,B_416)))
      | ~ v1_funct_1(C_417) ) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_2390,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | v1_partfun1('#skF_4',k2_struct_0('#skF_2'))
    | ~ v1_funct_2('#skF_4',k2_struct_0('#skF_2'),k2_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1758,c_2379])).

tff(c_2409,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | v1_partfun1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_1759,c_2390])).

tff(c_2410,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_1540,c_2409])).

tff(c_34,plain,(
    ! [A_40,B_41] :
      ( r1_tarski(A_40,B_41)
      | ~ m1_subset_1(A_40,k1_zfmisc_1(B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1009,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_999,c_34])).

tff(c_1757,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(k2_struct_0('#skF_2'),k2_relat_1('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1748,c_1009])).

tff(c_2422,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(k2_struct_0('#skF_2'),k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2410,c_1757])).

tff(c_2430,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2422])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( r2_hidden('#skF_1'(A_2,B_3),B_3)
      | r1_xboole_0(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_78,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_52,plain,(
    ! [A_54] : k10_relat_1(k1_xboole_0,A_54) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_58,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1577,plain,(
    ! [B_298,A_299] :
      ( k10_relat_1(B_298,k1_tarski(A_299)) != k1_xboole_0
      | ~ r2_hidden(A_299,k2_relat_1(B_298))
      | ~ v1_relat_1(B_298) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_1594,plain,(
    ! [A_299] :
      ( k10_relat_1(k1_xboole_0,k1_tarski(A_299)) != k1_xboole_0
      | ~ r2_hidden(A_299,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_1577])).

tff(c_1599,plain,(
    ! [A_300] : ~ r2_hidden(A_300,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_52,c_1594])).

tff(c_1628,plain,(
    ! [A_302] : r1_xboole_0(A_302,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_1599])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( ~ r1_xboole_0(B_8,A_7)
      | ~ r1_tarski(B_8,A_7)
      | v1_xboole_0(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1635,plain,(
    ! [A_302] :
      ( ~ r1_tarski(A_302,k1_xboole_0)
      | v1_xboole_0(A_302) ) ),
    inference(resolution,[status(thm)],[c_1628,c_10])).

tff(c_2482,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_2430,c_1635])).

tff(c_2500,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1209,c_2482])).

tff(c_2501,plain,(
    k2_struct_0('#skF_2') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1404])).

tff(c_54,plain,(
    ! [B_56,A_55] :
      ( k7_relat_1(B_56,A_55) = B_56
      | ~ v4_relat_1(B_56,A_55)
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1126,plain,
    ( k7_relat_1('#skF_4',k2_struct_0('#skF_2')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1092,c_54])).

tff(c_1129,plain,(
    k7_relat_1('#skF_4',k2_struct_0('#skF_2')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1008,c_1126])).

tff(c_48,plain,(
    ! [B_52,A_51] :
      ( k2_relat_1(k7_relat_1(B_52,A_51)) = k9_relat_1(B_52,A_51)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1145,plain,
    ( k9_relat_1('#skF_4',k2_struct_0('#skF_2')) = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1129,c_48])).

tff(c_1149,plain,(
    k9_relat_1('#skF_4',k2_struct_0('#skF_2')) = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1008,c_1145])).

tff(c_2505,plain,(
    k9_relat_1('#skF_4',k1_relat_1('#skF_4')) = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2501,c_1149])).

tff(c_7648,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) = k2_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_7590,c_2505])).

tff(c_7677,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1008,c_120,c_110,c_7648])).

tff(c_56,plain,(
    ! [A_57] :
      ( r1_tarski(A_57,k2_zfmisc_1(k1_relat_1(A_57),k2_relat_1(A_57)))
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_36,plain,(
    ! [A_40,B_41] :
      ( m1_subset_1(A_40,k1_zfmisc_1(B_41))
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1263,plain,(
    ! [A_266,A_267,B_268] :
      ( v4_relat_1(A_266,A_267)
      | ~ r1_tarski(A_266,k2_zfmisc_1(A_267,B_268)) ) ),
    inference(resolution,[status(thm)],[c_36,c_1074])).

tff(c_1280,plain,(
    ! [A_57] :
      ( v4_relat_1(A_57,k1_relat_1(A_57))
      | ~ v1_relat_1(A_57) ) ),
    inference(resolution,[status(thm)],[c_56,c_1263])).

tff(c_1357,plain,(
    ! [B_275] :
      ( v1_partfun1(B_275,k1_relat_1(B_275))
      | ~ v4_relat_1(B_275,k1_relat_1(B_275))
      | ~ v1_relat_1(B_275) ) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_1372,plain,(
    ! [A_57] :
      ( v1_partfun1(A_57,k1_relat_1(A_57))
      | ~ v1_relat_1(A_57) ) ),
    inference(resolution,[status(thm)],[c_1280,c_1357])).

tff(c_7832,plain,
    ( v1_partfun1(k2_funct_1('#skF_4'),k2_relat_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7677,c_1372])).

tff(c_7894,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_7832])).

tff(c_7897,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_7894])).

tff(c_7901,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1008,c_120,c_7897])).

tff(c_7903,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_7832])).

tff(c_7838,plain,
    ( v4_relat_1(k2_funct_1('#skF_4'),k2_relat_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7677,c_1280])).

tff(c_7911,plain,(
    v4_relat_1(k2_funct_1('#skF_4'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7903,c_7838])).

tff(c_7917,plain,
    ( k7_relat_1(k2_funct_1('#skF_4'),k2_relat_1('#skF_4')) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_7911,c_54])).

tff(c_7923,plain,(
    k7_relat_1(k2_funct_1('#skF_4'),k2_relat_1('#skF_4')) = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7903,c_7917])).

tff(c_7954,plain,
    ( k9_relat_1(k2_funct_1('#skF_4'),k2_relat_1('#skF_4')) = k2_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7923,c_48])).

tff(c_7980,plain,(
    k9_relat_1(k2_funct_1('#skF_4'),k2_relat_1('#skF_4')) = k2_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7903,c_7954])).

tff(c_1042,plain,(
    ! [A_228] :
      ( r1_tarski(A_228,k2_zfmisc_1(k1_relat_1(A_228),k2_relat_1(A_228)))
      | ~ v1_relat_1(A_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1048,plain,(
    ! [B_52,A_51] :
      ( r1_tarski(k7_relat_1(B_52,A_51),k2_zfmisc_1(k1_relat_1(k7_relat_1(B_52,A_51)),k9_relat_1(B_52,A_51)))
      | ~ v1_relat_1(k7_relat_1(B_52,A_51))
      | ~ v1_relat_1(B_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_1042])).

tff(c_8034,plain,
    ( r1_tarski(k7_relat_1(k2_funct_1('#skF_4'),k2_relat_1('#skF_4')),k2_zfmisc_1(k1_relat_1(k7_relat_1(k2_funct_1('#skF_4'),k2_relat_1('#skF_4'))),k2_relat_1(k2_funct_1('#skF_4'))))
    | ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_4'),k2_relat_1('#skF_4')))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7980,c_1048])).

tff(c_8054,plain,(
    r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1(k2_relat_1('#skF_4'),k2_relat_1(k2_funct_1('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7903,c_7903,c_7923,c_7677,c_7923,c_7923,c_8034])).

tff(c_8260,plain,
    ( r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4')))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_8054])).

tff(c_8275,plain,(
    r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1008,c_120,c_110,c_8260])).

tff(c_3414,plain,(
    ! [A_522,B_523,C_524,D_525] :
      ( k8_relset_1(A_522,B_523,C_524,D_525) = k10_relat_1(C_524,D_525)
      | ~ m1_subset_1(C_524,k1_zfmisc_1(k2_zfmisc_1(A_522,B_523))) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_3436,plain,(
    ! [A_522,B_523,A_40,D_525] :
      ( k8_relset_1(A_522,B_523,A_40,D_525) = k10_relat_1(A_40,D_525)
      | ~ r1_tarski(A_40,k2_zfmisc_1(A_522,B_523)) ) ),
    inference(resolution,[status(thm)],[c_36,c_3414])).

tff(c_8301,plain,(
    ! [D_525] : k8_relset_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_funct_1('#skF_4'),D_525) = k10_relat_1(k2_funct_1('#skF_4'),D_525) ),
    inference(resolution,[status(thm)],[c_8275,c_3436])).

tff(c_2510,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k2_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2501,c_999])).

tff(c_2901,plain,(
    ! [A_449,B_450,C_451] :
      ( k2_relset_1(A_449,B_450,C_451) = k2_relat_1(C_451)
      | ~ m1_subset_1(C_451,k1_zfmisc_1(k2_zfmisc_1(A_449,B_450))) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_2929,plain,(
    k2_relset_1(k1_relat_1('#skF_4'),k2_struct_0('#skF_3'),'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2510,c_2901])).

tff(c_2513,plain,(
    k2_relset_1(k1_relat_1('#skF_4'),k2_struct_0('#skF_3'),'#skF_4') = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2501,c_244])).

tff(c_2940,plain,(
    k2_struct_0('#skF_3') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2929,c_2513])).

tff(c_2514,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2501,c_221])).

tff(c_2950,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2940,c_2514])).

tff(c_2945,plain,(
    k2_relset_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2940,c_2929])).

tff(c_2948,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2940,c_2510])).

tff(c_3783,plain,(
    ! [A_578,B_579,C_580] :
      ( k2_tops_2(A_578,B_579,C_580) = k2_funct_1(C_580)
      | ~ v2_funct_1(C_580)
      | k2_relset_1(A_578,B_579,C_580) != B_579
      | ~ m1_subset_1(C_580,k1_zfmisc_1(k2_zfmisc_1(A_578,B_579)))
      | ~ v1_funct_2(C_580,A_578,B_579)
      | ~ v1_funct_1(C_580) ) ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_3786,plain,
    ( k2_tops_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') = k2_funct_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') != k2_relat_1('#skF_4')
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2948,c_3783])).

tff(c_3811,plain,(
    k2_tops_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_2950,c_2945,c_110,c_3786])).

tff(c_3207,plain,(
    ! [A_479,B_480,C_481,D_482] :
      ( k7_relset_1(A_479,B_480,C_481,D_482) = k9_relat_1(C_481,D_482)
      | ~ m1_subset_1(C_481,k1_zfmisc_1(k2_zfmisc_1(A_479,B_480))) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_3226,plain,(
    ! [D_482] : k7_relset_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4',D_482) = k9_relat_1('#skF_4',D_482) ),
    inference(resolution,[status(thm)],[c_2948,c_3207])).

tff(c_108,plain,(
    k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4'),'#skF_5') != k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_1062,plain,(
    k8_relset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'),'#skF_4'),'#skF_5') != k7_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'),'#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_200,c_200,c_201,c_201,c_201,c_108])).

tff(c_2508,plain,(
    k8_relset_1(k2_struct_0('#skF_3'),k1_relat_1('#skF_4'),k2_tops_2(k1_relat_1('#skF_4'),k2_struct_0('#skF_3'),'#skF_4'),'#skF_5') != k7_relset_1(k1_relat_1('#skF_4'),k2_struct_0('#skF_3'),'#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2501,c_2501,c_2501,c_1062])).

tff(c_2947,plain,(
    k8_relset_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_tops_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4'),'#skF_5') != k7_relset_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2940,c_2940,c_2940,c_2508])).

tff(c_3239,plain,(
    k8_relset_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_tops_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4'),'#skF_5') != k9_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3226,c_2947])).

tff(c_3818,plain,(
    k8_relset_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_funct_1('#skF_4'),'#skF_5') != k9_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3811,c_3239])).

tff(c_8367,plain,(
    k10_relat_1(k2_funct_1('#skF_4'),'#skF_5') != k9_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8301,c_3818])).

tff(c_8379,plain,
    ( ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_8367])).

tff(c_8383,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1008,c_120,c_110,c_8379])).

tff(c_8385,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1202])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8406,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_8385,c_2])).

tff(c_8421,plain,(
    ! [A_54] : k10_relat_1('#skF_4',A_54) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8406,c_8406,c_52])).

tff(c_32,plain,(
    ! [A_39] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_39)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_8419,plain,(
    ! [A_39] : m1_subset_1('#skF_4',k1_zfmisc_1(A_39)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8406,c_32])).

tff(c_9175,plain,(
    ! [A_965,B_966,C_967,D_968] :
      ( k8_relset_1(A_965,B_966,C_967,D_968) = k10_relat_1(C_967,D_968)
      | ~ m1_subset_1(C_967,k1_zfmisc_1(k2_zfmisc_1(A_965,B_966))) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_9178,plain,(
    ! [A_965,B_966,D_968] : k8_relset_1(A_965,B_966,'#skF_4',D_968) = k10_relat_1('#skF_4',D_968) ),
    inference(resolution,[status(thm)],[c_8419,c_9175])).

tff(c_9187,plain,(
    ! [A_965,B_966,D_968] : k8_relset_1(A_965,B_966,'#skF_4',D_968) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8421,c_9178])).

tff(c_8424,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8406,c_8406,c_58])).

tff(c_8901,plain,(
    ! [A_928,B_929,C_930] :
      ( k2_relset_1(A_928,B_929,C_930) = k2_relat_1(C_930)
      | ~ m1_subset_1(C_930,k1_zfmisc_1(k2_zfmisc_1(A_928,B_929))) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_8905,plain,(
    ! [A_928,B_929] : k2_relset_1(A_928,B_929,'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8419,c_8901])).

tff(c_8917,plain,(
    ! [A_928,B_929] : k2_relset_1(A_928,B_929,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8424,c_8905])).

tff(c_8919,plain,(
    k2_struct_0('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8917,c_244])).

tff(c_8928,plain,(
    v1_funct_2('#skF_4',k2_struct_0('#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8919,c_221])).

tff(c_183,plain,(
    ! [A_110] :
      ( v1_xboole_0(k4_relat_1(A_110))
      | ~ v1_xboole_0(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_187,plain,(
    ! [A_110] :
      ( k4_relat_1(A_110) = k1_xboole_0
      | ~ v1_xboole_0(A_110) ) ),
    inference(resolution,[status(thm)],[c_183,c_2])).

tff(c_8405,plain,(
    k4_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8385,c_187])).

tff(c_8454,plain,(
    k4_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8406,c_8405])).

tff(c_8455,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8454,c_1195])).

tff(c_9619,plain,(
    ! [A_1035,B_1036,C_1037] :
      ( k2_tops_2(A_1035,B_1036,C_1037) = k2_funct_1(C_1037)
      | ~ v2_funct_1(C_1037)
      | k2_relset_1(A_1035,B_1036,C_1037) != B_1036
      | ~ m1_subset_1(C_1037,k1_zfmisc_1(k2_zfmisc_1(A_1035,B_1036)))
      | ~ v1_funct_2(C_1037,A_1035,B_1036)
      | ~ v1_funct_1(C_1037) ) ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_9631,plain,(
    ! [A_1035,B_1036] :
      ( k2_tops_2(A_1035,B_1036,'#skF_4') = k2_funct_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | k2_relset_1(A_1035,B_1036,'#skF_4') != B_1036
      | ~ v1_funct_2('#skF_4',A_1035,B_1036)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_8419,c_9619])).

tff(c_9649,plain,(
    ! [A_1038,B_1039] :
      ( k2_tops_2(A_1038,B_1039,'#skF_4') = '#skF_4'
      | B_1039 != '#skF_4'
      | ~ v1_funct_2('#skF_4',A_1038,B_1039) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_8917,c_110,c_8455,c_9631])).

tff(c_9653,plain,(
    k2_tops_2(k2_struct_0('#skF_2'),'#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_8928,c_9649])).

tff(c_1095,plain,(
    ! [A_240] : v4_relat_1(k1_xboole_0,A_240) ),
    inference(resolution,[status(thm)],[c_32,c_1074])).

tff(c_1098,plain,(
    ! [A_240] :
      ( k7_relat_1(k1_xboole_0,A_240) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1095,c_54])).

tff(c_1130,plain,(
    ! [A_244] : k7_relat_1(k1_xboole_0,A_244) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1098])).

tff(c_1135,plain,(
    ! [A_244] :
      ( k9_relat_1(k1_xboole_0,A_244) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1130,c_48])).

tff(c_1140,plain,(
    ! [A_244] : k9_relat_1(k1_xboole_0,A_244) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_58,c_1135])).

tff(c_8410,plain,(
    ! [A_244] : k9_relat_1('#skF_4',A_244) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8406,c_8406,c_1140])).

tff(c_9212,plain,(
    ! [A_976,B_977,C_978,D_979] :
      ( k7_relset_1(A_976,B_977,C_978,D_979) = k9_relat_1(C_978,D_979)
      | ~ m1_subset_1(C_978,k1_zfmisc_1(k2_zfmisc_1(A_976,B_977))) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_9215,plain,(
    ! [A_976,B_977,D_979] : k7_relset_1(A_976,B_977,'#skF_4',D_979) = k9_relat_1('#skF_4',D_979) ),
    inference(resolution,[status(thm)],[c_8419,c_9212])).

tff(c_9224,plain,(
    ! [A_976,B_977,D_979] : k7_relset_1(A_976,B_977,'#skF_4',D_979) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8410,c_9215])).

tff(c_8927,plain,(
    k8_relset_1('#skF_4',k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),'#skF_4','#skF_4'),'#skF_5') != k7_relset_1(k2_struct_0('#skF_2'),'#skF_4','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8919,c_8919,c_8919,c_1062])).

tff(c_9226,plain,(
    k8_relset_1('#skF_4',k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),'#skF_4','#skF_4'),'#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9224,c_8927])).

tff(c_9654,plain,(
    k8_relset_1('#skF_4',k2_struct_0('#skF_2'),'#skF_4','#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9653,c_9226])).

tff(c_9657,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9187,c_9654])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:51:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.28/3.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.28/3.09  
% 8.28/3.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.28/3.09  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v5_ordinal1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k8_relset_1 > k7_relset_1 > k2_enumset1 > k2_tops_2 > k2_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > u1_struct_0 > k4_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 8.28/3.09  
% 8.28/3.09  %Foreground sorts:
% 8.28/3.09  
% 8.28/3.09  
% 8.28/3.09  %Background operators:
% 8.28/3.09  
% 8.28/3.09  
% 8.28/3.09  %Foreground operators:
% 8.28/3.09  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.28/3.09  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.28/3.09  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 8.28/3.09  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.28/3.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.28/3.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.28/3.09  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.28/3.09  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 8.28/3.09  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 8.28/3.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.28/3.09  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.28/3.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.28/3.09  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.28/3.09  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.28/3.09  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 8.28/3.09  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 8.28/3.09  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 8.28/3.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.28/3.09  tff('#skF_5', type, '#skF_5': $i).
% 8.28/3.09  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.28/3.09  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.28/3.09  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.28/3.09  tff('#skF_2', type, '#skF_2': $i).
% 8.28/3.09  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 8.28/3.09  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 8.28/3.09  tff('#skF_3', type, '#skF_3': $i).
% 8.28/3.09  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.28/3.09  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.28/3.09  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.28/3.09  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 8.28/3.09  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 8.28/3.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.28/3.09  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 8.28/3.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.28/3.09  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.28/3.09  tff('#skF_4', type, '#skF_4': $i).
% 8.28/3.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.28/3.09  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.28/3.09  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.28/3.09  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.28/3.09  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.28/3.09  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 8.28/3.09  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.28/3.09  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.28/3.09  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 8.28/3.09  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.28/3.09  
% 8.67/3.12  tff(f_102, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.67/3.12  tff(f_255, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => (k7_relset_1(u1_struct_0(A), u1_struct_0(B), C, D) = k8_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C), D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_tops_2)).
% 8.67/3.12  tff(f_221, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 8.67/3.12  tff(f_94, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 8.67/3.12  tff(f_156, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k9_relat_1(B, A) = k10_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t154_funct_1)).
% 8.67/3.12  tff(f_166, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 8.67/3.12  tff(f_141, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 8.67/3.12  tff(f_110, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 8.67/3.12  tff(f_133, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 8.67/3.12  tff(f_100, axiom, (![A]: (v1_xboole_0(A) => (v1_xboole_0(k4_relat_1(A)) & v1_relat_1(k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_relat_1)).
% 8.67/3.12  tff(f_75, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.67/3.12  tff(f_180, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.67/3.12  tff(f_200, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 8.67/3.12  tff(f_184, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.67/3.12  tff(f_217, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_funct_2)).
% 8.67/3.12  tff(f_81, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 8.67/3.12  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 8.67/3.12  tff(f_174, axiom, (![A]: (((v1_relat_1(k1_xboole_0) & v5_relat_1(k1_xboole_0, A)) & v1_funct_1(k1_xboole_0)) & v5_ordinal1(k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_ordinal1)).
% 8.67/3.12  tff(f_112, axiom, (![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 8.67/3.12  tff(f_125, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 8.67/3.12  tff(f_148, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_1)).
% 8.67/3.12  tff(f_55, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 8.67/3.12  tff(f_118, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 8.67/3.12  tff(f_106, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 8.67/3.12  tff(f_122, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 8.67/3.12  tff(f_192, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 8.67/3.12  tff(f_233, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 8.67/3.12  tff(f_188, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 8.67/3.12  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 8.67/3.12  tff(f_77, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 8.67/3.12  tff(c_46, plain, (![A_49, B_50]: (v1_relat_1(k2_zfmisc_1(A_49, B_50)))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.67/3.12  tff(c_122, plain, (l1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_255])).
% 8.67/3.12  tff(c_193, plain, (![A_112]: (u1_struct_0(A_112)=k2_struct_0(A_112) | ~l1_struct_0(A_112))), inference(cnfTransformation, [status(thm)], [f_221])).
% 8.67/3.12  tff(c_200, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_122, c_193])).
% 8.67/3.12  tff(c_124, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_255])).
% 8.67/3.12  tff(c_201, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_124, c_193])).
% 8.67/3.12  tff(c_116, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_255])).
% 8.67/3.12  tff(c_999, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_200, c_201, c_116])).
% 8.67/3.12  tff(c_40, plain, (![B_47, A_45]: (v1_relat_1(B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(A_45)) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.67/3.12  tff(c_1002, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_999, c_40])).
% 8.67/3.12  tff(c_1008, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1002])).
% 8.67/3.12  tff(c_120, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_255])).
% 8.67/3.12  tff(c_110, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_255])).
% 8.67/3.12  tff(c_72, plain, (![B_63, A_62]: (k10_relat_1(k2_funct_1(B_63), A_62)=k9_relat_1(B_63, A_62) | ~v2_funct_1(B_63) | ~v1_funct_1(B_63) | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_156])).
% 8.67/3.12  tff(c_74, plain, (![A_64]: (k2_relat_1(k2_funct_1(A_64))=k1_relat_1(A_64) | ~v2_funct_1(A_64) | ~v1_funct_1(A_64) | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_166])).
% 8.67/3.12  tff(c_66, plain, (![A_59]: (v1_relat_1(k2_funct_1(A_59)) | ~v1_funct_1(A_59) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_141])).
% 8.67/3.12  tff(c_1503, plain, (![A_288]: (k2_relat_1(k2_funct_1(A_288))=k1_relat_1(A_288) | ~v2_funct_1(A_288) | ~v1_funct_1(A_288) | ~v1_relat_1(A_288))), inference(cnfTransformation, [status(thm)], [f_166])).
% 8.67/3.12  tff(c_50, plain, (![A_53]: (k10_relat_1(A_53, k2_relat_1(A_53))=k1_relat_1(A_53) | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_110])).
% 8.67/3.12  tff(c_4167, plain, (![A_623]: (k10_relat_1(k2_funct_1(A_623), k1_relat_1(A_623))=k1_relat_1(k2_funct_1(A_623)) | ~v1_relat_1(k2_funct_1(A_623)) | ~v2_funct_1(A_623) | ~v1_funct_1(A_623) | ~v1_relat_1(A_623))), inference(superposition, [status(thm), theory('equality')], [c_1503, c_50])).
% 8.67/3.12  tff(c_7586, plain, (![A_873]: (k9_relat_1(A_873, k1_relat_1(A_873))=k1_relat_1(k2_funct_1(A_873)) | ~v2_funct_1(A_873) | ~v1_funct_1(A_873) | ~v1_relat_1(A_873) | ~v1_relat_1(k2_funct_1(A_873)) | ~v2_funct_1(A_873) | ~v1_funct_1(A_873) | ~v1_relat_1(A_873))), inference(superposition, [status(thm), theory('equality')], [c_4167, c_72])).
% 8.67/3.12  tff(c_7590, plain, (![A_874]: (k9_relat_1(A_874, k1_relat_1(A_874))=k1_relat_1(k2_funct_1(A_874)) | ~v2_funct_1(A_874) | ~v1_funct_1(A_874) | ~v1_relat_1(A_874))), inference(resolution, [status(thm)], [c_66, c_7586])).
% 8.67/3.12  tff(c_1189, plain, (![A_250]: (k4_relat_1(A_250)=k2_funct_1(A_250) | ~v2_funct_1(A_250) | ~v1_funct_1(A_250) | ~v1_relat_1(A_250))), inference(cnfTransformation, [status(thm)], [f_133])).
% 8.67/3.12  tff(c_1192, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_110, c_1189])).
% 8.67/3.12  tff(c_1195, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1008, c_120, c_1192])).
% 8.67/3.12  tff(c_44, plain, (![A_48]: (v1_xboole_0(k4_relat_1(A_48)) | ~v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.67/3.12  tff(c_1202, plain, (v1_xboole_0(k2_funct_1('#skF_4')) | ~v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1195, c_44])).
% 8.67/3.12  tff(c_1209, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_1202])).
% 8.67/3.12  tff(c_28, plain, (![A_37]: (k2_zfmisc_1(A_37, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.67/3.12  tff(c_1074, plain, (![C_237, A_238, B_239]: (v4_relat_1(C_237, A_238) | ~m1_subset_1(C_237, k1_zfmisc_1(k2_zfmisc_1(A_238, B_239))))), inference(cnfTransformation, [status(thm)], [f_180])).
% 8.67/3.12  tff(c_1092, plain, (v4_relat_1('#skF_4', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_999, c_1074])).
% 8.67/3.12  tff(c_1386, plain, (![B_277, A_278]: (k1_relat_1(B_277)=A_278 | ~v1_partfun1(B_277, A_278) | ~v4_relat_1(B_277, A_278) | ~v1_relat_1(B_277))), inference(cnfTransformation, [status(thm)], [f_200])).
% 8.67/3.12  tff(c_1395, plain, (k2_struct_0('#skF_2')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', k2_struct_0('#skF_2')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1092, c_1386])).
% 8.67/3.12  tff(c_1404, plain, (k2_struct_0('#skF_2')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1008, c_1395])).
% 8.67/3.12  tff(c_1540, plain, (~v1_partfun1('#skF_4', k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1404])).
% 8.67/3.12  tff(c_1719, plain, (![A_316, B_317, C_318]: (k2_relset_1(A_316, B_317, C_318)=k2_relat_1(C_318) | ~m1_subset_1(C_318, k1_zfmisc_1(k2_zfmisc_1(A_316, B_317))))), inference(cnfTransformation, [status(thm)], [f_184])).
% 8.67/3.12  tff(c_1737, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'), '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_999, c_1719])).
% 8.67/3.12  tff(c_112, plain, (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')=k2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_255])).
% 8.67/3.12  tff(c_244, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'), '#skF_4')=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_201, c_200, c_112])).
% 8.67/3.12  tff(c_1748, plain, (k2_struct_0('#skF_3')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1737, c_244])).
% 8.67/3.12  tff(c_118, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_255])).
% 8.67/3.12  tff(c_202, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_200, c_118])).
% 8.67/3.12  tff(c_221, plain, (v1_funct_2('#skF_4', k2_struct_0('#skF_2'), k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_201, c_202])).
% 8.67/3.12  tff(c_1759, plain, (v1_funct_2('#skF_4', k2_struct_0('#skF_2'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1748, c_221])).
% 8.67/3.12  tff(c_1758, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_relat_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_1748, c_999])).
% 8.67/3.12  tff(c_2379, plain, (![B_416, C_417, A_418]: (k1_xboole_0=B_416 | v1_partfun1(C_417, A_418) | ~v1_funct_2(C_417, A_418, B_416) | ~m1_subset_1(C_417, k1_zfmisc_1(k2_zfmisc_1(A_418, B_416))) | ~v1_funct_1(C_417))), inference(cnfTransformation, [status(thm)], [f_217])).
% 8.67/3.12  tff(c_2390, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | v1_partfun1('#skF_4', k2_struct_0('#skF_2')) | ~v1_funct_2('#skF_4', k2_struct_0('#skF_2'), k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_1758, c_2379])).
% 8.67/3.12  tff(c_2409, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | v1_partfun1('#skF_4', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_1759, c_2390])).
% 8.67/3.12  tff(c_2410, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_1540, c_2409])).
% 8.67/3.12  tff(c_34, plain, (![A_40, B_41]: (r1_tarski(A_40, B_41) | ~m1_subset_1(A_40, k1_zfmisc_1(B_41)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.67/3.12  tff(c_1009, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_999, c_34])).
% 8.67/3.12  tff(c_1757, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k2_struct_0('#skF_2'), k2_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1748, c_1009])).
% 8.67/3.12  tff(c_2422, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k2_struct_0('#skF_2'), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2410, c_1757])).
% 8.67/3.12  tff(c_2430, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_2422])).
% 8.67/3.12  tff(c_6, plain, (![A_2, B_3]: (r2_hidden('#skF_1'(A_2, B_3), B_3) | r1_xboole_0(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.67/3.12  tff(c_78, plain, (v1_relat_1(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_174])).
% 8.67/3.12  tff(c_52, plain, (![A_54]: (k10_relat_1(k1_xboole_0, A_54)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.67/3.12  tff(c_58, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.67/3.12  tff(c_1577, plain, (![B_298, A_299]: (k10_relat_1(B_298, k1_tarski(A_299))!=k1_xboole_0 | ~r2_hidden(A_299, k2_relat_1(B_298)) | ~v1_relat_1(B_298))), inference(cnfTransformation, [status(thm)], [f_148])).
% 8.67/3.12  tff(c_1594, plain, (![A_299]: (k10_relat_1(k1_xboole_0, k1_tarski(A_299))!=k1_xboole_0 | ~r2_hidden(A_299, k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_58, c_1577])).
% 8.67/3.12  tff(c_1599, plain, (![A_300]: (~r2_hidden(A_300, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_52, c_1594])).
% 8.67/3.12  tff(c_1628, plain, (![A_302]: (r1_xboole_0(A_302, k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_1599])).
% 8.67/3.12  tff(c_10, plain, (![B_8, A_7]: (~r1_xboole_0(B_8, A_7) | ~r1_tarski(B_8, A_7) | v1_xboole_0(B_8))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.67/3.12  tff(c_1635, plain, (![A_302]: (~r1_tarski(A_302, k1_xboole_0) | v1_xboole_0(A_302))), inference(resolution, [status(thm)], [c_1628, c_10])).
% 8.67/3.12  tff(c_2482, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_2430, c_1635])).
% 8.67/3.12  tff(c_2500, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1209, c_2482])).
% 8.67/3.12  tff(c_2501, plain, (k2_struct_0('#skF_2')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_1404])).
% 8.67/3.12  tff(c_54, plain, (![B_56, A_55]: (k7_relat_1(B_56, A_55)=B_56 | ~v4_relat_1(B_56, A_55) | ~v1_relat_1(B_56))), inference(cnfTransformation, [status(thm)], [f_118])).
% 8.67/3.12  tff(c_1126, plain, (k7_relat_1('#skF_4', k2_struct_0('#skF_2'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1092, c_54])).
% 8.67/3.12  tff(c_1129, plain, (k7_relat_1('#skF_4', k2_struct_0('#skF_2'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1008, c_1126])).
% 8.67/3.12  tff(c_48, plain, (![B_52, A_51]: (k2_relat_1(k7_relat_1(B_52, A_51))=k9_relat_1(B_52, A_51) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_106])).
% 8.67/3.12  tff(c_1145, plain, (k9_relat_1('#skF_4', k2_struct_0('#skF_2'))=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1129, c_48])).
% 8.67/3.12  tff(c_1149, plain, (k9_relat_1('#skF_4', k2_struct_0('#skF_2'))=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1008, c_1145])).
% 8.67/3.12  tff(c_2505, plain, (k9_relat_1('#skF_4', k1_relat_1('#skF_4'))=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2501, c_1149])).
% 8.67/3.12  tff(c_7648, plain, (k1_relat_1(k2_funct_1('#skF_4'))=k2_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_7590, c_2505])).
% 8.67/3.12  tff(c_7677, plain, (k1_relat_1(k2_funct_1('#skF_4'))=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1008, c_120, c_110, c_7648])).
% 8.67/3.12  tff(c_56, plain, (![A_57]: (r1_tarski(A_57, k2_zfmisc_1(k1_relat_1(A_57), k2_relat_1(A_57))) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_122])).
% 8.67/3.12  tff(c_36, plain, (![A_40, B_41]: (m1_subset_1(A_40, k1_zfmisc_1(B_41)) | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.67/3.12  tff(c_1263, plain, (![A_266, A_267, B_268]: (v4_relat_1(A_266, A_267) | ~r1_tarski(A_266, k2_zfmisc_1(A_267, B_268)))), inference(resolution, [status(thm)], [c_36, c_1074])).
% 8.67/3.12  tff(c_1280, plain, (![A_57]: (v4_relat_1(A_57, k1_relat_1(A_57)) | ~v1_relat_1(A_57))), inference(resolution, [status(thm)], [c_56, c_1263])).
% 8.67/3.12  tff(c_1357, plain, (![B_275]: (v1_partfun1(B_275, k1_relat_1(B_275)) | ~v4_relat_1(B_275, k1_relat_1(B_275)) | ~v1_relat_1(B_275))), inference(cnfTransformation, [status(thm)], [f_200])).
% 8.67/3.12  tff(c_1372, plain, (![A_57]: (v1_partfun1(A_57, k1_relat_1(A_57)) | ~v1_relat_1(A_57))), inference(resolution, [status(thm)], [c_1280, c_1357])).
% 8.67/3.12  tff(c_7832, plain, (v1_partfun1(k2_funct_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7677, c_1372])).
% 8.67/3.12  tff(c_7894, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_7832])).
% 8.67/3.12  tff(c_7897, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_7894])).
% 8.67/3.12  tff(c_7901, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1008, c_120, c_7897])).
% 8.67/3.12  tff(c_7903, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_7832])).
% 8.67/3.12  tff(c_7838, plain, (v4_relat_1(k2_funct_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7677, c_1280])).
% 8.67/3.12  tff(c_7911, plain, (v4_relat_1(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_7903, c_7838])).
% 8.67/3.12  tff(c_7917, plain, (k7_relat_1(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_7911, c_54])).
% 8.67/3.12  tff(c_7923, plain, (k7_relat_1(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'))=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7903, c_7917])).
% 8.67/3.12  tff(c_7954, plain, (k9_relat_1(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'))=k2_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7923, c_48])).
% 8.67/3.12  tff(c_7980, plain, (k9_relat_1(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'))=k2_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_7903, c_7954])).
% 8.67/3.12  tff(c_1042, plain, (![A_228]: (r1_tarski(A_228, k2_zfmisc_1(k1_relat_1(A_228), k2_relat_1(A_228))) | ~v1_relat_1(A_228))), inference(cnfTransformation, [status(thm)], [f_122])).
% 8.67/3.12  tff(c_1048, plain, (![B_52, A_51]: (r1_tarski(k7_relat_1(B_52, A_51), k2_zfmisc_1(k1_relat_1(k7_relat_1(B_52, A_51)), k9_relat_1(B_52, A_51))) | ~v1_relat_1(k7_relat_1(B_52, A_51)) | ~v1_relat_1(B_52))), inference(superposition, [status(thm), theory('equality')], [c_48, c_1042])).
% 8.67/3.12  tff(c_8034, plain, (r1_tarski(k7_relat_1(k2_funct_1('#skF_4'), k2_relat_1('#skF_4')), k2_zfmisc_1(k1_relat_1(k7_relat_1(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'))), k2_relat_1(k2_funct_1('#skF_4')))) | ~v1_relat_1(k7_relat_1(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'))) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7980, c_1048])).
% 8.67/3.12  tff(c_8054, plain, (r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1(k2_relat_1('#skF_4'), k2_relat_1(k2_funct_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_7903, c_7903, c_7923, c_7677, c_7923, c_7923, c_8034])).
% 8.67/3.12  tff(c_8260, plain, (r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'))) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_74, c_8054])).
% 8.67/3.12  tff(c_8275, plain, (r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1008, c_120, c_110, c_8260])).
% 8.67/3.12  tff(c_3414, plain, (![A_522, B_523, C_524, D_525]: (k8_relset_1(A_522, B_523, C_524, D_525)=k10_relat_1(C_524, D_525) | ~m1_subset_1(C_524, k1_zfmisc_1(k2_zfmisc_1(A_522, B_523))))), inference(cnfTransformation, [status(thm)], [f_192])).
% 8.67/3.12  tff(c_3436, plain, (![A_522, B_523, A_40, D_525]: (k8_relset_1(A_522, B_523, A_40, D_525)=k10_relat_1(A_40, D_525) | ~r1_tarski(A_40, k2_zfmisc_1(A_522, B_523)))), inference(resolution, [status(thm)], [c_36, c_3414])).
% 8.67/3.12  tff(c_8301, plain, (![D_525]: (k8_relset_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_funct_1('#skF_4'), D_525)=k10_relat_1(k2_funct_1('#skF_4'), D_525))), inference(resolution, [status(thm)], [c_8275, c_3436])).
% 8.67/3.12  tff(c_2510, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_2501, c_999])).
% 8.67/3.12  tff(c_2901, plain, (![A_449, B_450, C_451]: (k2_relset_1(A_449, B_450, C_451)=k2_relat_1(C_451) | ~m1_subset_1(C_451, k1_zfmisc_1(k2_zfmisc_1(A_449, B_450))))), inference(cnfTransformation, [status(thm)], [f_184])).
% 8.67/3.12  tff(c_2929, plain, (k2_relset_1(k1_relat_1('#skF_4'), k2_struct_0('#skF_3'), '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2510, c_2901])).
% 8.67/3.12  tff(c_2513, plain, (k2_relset_1(k1_relat_1('#skF_4'), k2_struct_0('#skF_3'), '#skF_4')=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2501, c_244])).
% 8.67/3.12  tff(c_2940, plain, (k2_struct_0('#skF_3')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2929, c_2513])).
% 8.67/3.12  tff(c_2514, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2501, c_221])).
% 8.67/3.12  tff(c_2950, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2940, c_2514])).
% 8.67/3.12  tff(c_2945, plain, (k2_relset_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2940, c_2929])).
% 8.67/3.12  tff(c_2948, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_2940, c_2510])).
% 8.67/3.12  tff(c_3783, plain, (![A_578, B_579, C_580]: (k2_tops_2(A_578, B_579, C_580)=k2_funct_1(C_580) | ~v2_funct_1(C_580) | k2_relset_1(A_578, B_579, C_580)!=B_579 | ~m1_subset_1(C_580, k1_zfmisc_1(k2_zfmisc_1(A_578, B_579))) | ~v1_funct_2(C_580, A_578, B_579) | ~v1_funct_1(C_580))), inference(cnfTransformation, [status(thm)], [f_233])).
% 8.67/3.12  tff(c_3786, plain, (k2_tops_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')=k2_funct_1('#skF_4') | ~v2_funct_1('#skF_4') | k2_relset_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')!=k2_relat_1('#skF_4') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_2948, c_3783])).
% 8.67/3.12  tff(c_3811, plain, (k2_tops_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_2950, c_2945, c_110, c_3786])).
% 8.67/3.12  tff(c_3207, plain, (![A_479, B_480, C_481, D_482]: (k7_relset_1(A_479, B_480, C_481, D_482)=k9_relat_1(C_481, D_482) | ~m1_subset_1(C_481, k1_zfmisc_1(k2_zfmisc_1(A_479, B_480))))), inference(cnfTransformation, [status(thm)], [f_188])).
% 8.67/3.12  tff(c_3226, plain, (![D_482]: (k7_relset_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4', D_482)=k9_relat_1('#skF_4', D_482))), inference(resolution, [status(thm)], [c_2948, c_3207])).
% 8.67/3.12  tff(c_108, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4'), '#skF_5')!=k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_255])).
% 8.67/3.12  tff(c_1062, plain, (k8_relset_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'), '#skF_4'), '#skF_5')!=k7_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'), '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_200, c_200, c_200, c_201, c_201, c_201, c_108])).
% 8.67/3.12  tff(c_2508, plain, (k8_relset_1(k2_struct_0('#skF_3'), k1_relat_1('#skF_4'), k2_tops_2(k1_relat_1('#skF_4'), k2_struct_0('#skF_3'), '#skF_4'), '#skF_5')!=k7_relset_1(k1_relat_1('#skF_4'), k2_struct_0('#skF_3'), '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2501, c_2501, c_2501, c_1062])).
% 8.67/3.12  tff(c_2947, plain, (k8_relset_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_tops_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4'), '#skF_5')!=k7_relset_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2940, c_2940, c_2940, c_2508])).
% 8.67/3.12  tff(c_3239, plain, (k8_relset_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_tops_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4'), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3226, c_2947])).
% 8.67/3.12  tff(c_3818, plain, (k8_relset_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_funct_1('#skF_4'), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3811, c_3239])).
% 8.67/3.12  tff(c_8367, plain, (k10_relat_1(k2_funct_1('#skF_4'), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8301, c_3818])).
% 8.67/3.12  tff(c_8379, plain, (~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_72, c_8367])).
% 8.67/3.12  tff(c_8383, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1008, c_120, c_110, c_8379])).
% 8.67/3.12  tff(c_8385, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_1202])).
% 8.67/3.12  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.67/3.12  tff(c_8406, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_8385, c_2])).
% 8.67/3.12  tff(c_8421, plain, (![A_54]: (k10_relat_1('#skF_4', A_54)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8406, c_8406, c_52])).
% 8.67/3.12  tff(c_32, plain, (![A_39]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.67/3.12  tff(c_8419, plain, (![A_39]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_39)))), inference(demodulation, [status(thm), theory('equality')], [c_8406, c_32])).
% 8.67/3.12  tff(c_9175, plain, (![A_965, B_966, C_967, D_968]: (k8_relset_1(A_965, B_966, C_967, D_968)=k10_relat_1(C_967, D_968) | ~m1_subset_1(C_967, k1_zfmisc_1(k2_zfmisc_1(A_965, B_966))))), inference(cnfTransformation, [status(thm)], [f_192])).
% 8.67/3.12  tff(c_9178, plain, (![A_965, B_966, D_968]: (k8_relset_1(A_965, B_966, '#skF_4', D_968)=k10_relat_1('#skF_4', D_968))), inference(resolution, [status(thm)], [c_8419, c_9175])).
% 8.67/3.12  tff(c_9187, plain, (![A_965, B_966, D_968]: (k8_relset_1(A_965, B_966, '#skF_4', D_968)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8421, c_9178])).
% 8.67/3.12  tff(c_8424, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8406, c_8406, c_58])).
% 8.67/3.12  tff(c_8901, plain, (![A_928, B_929, C_930]: (k2_relset_1(A_928, B_929, C_930)=k2_relat_1(C_930) | ~m1_subset_1(C_930, k1_zfmisc_1(k2_zfmisc_1(A_928, B_929))))), inference(cnfTransformation, [status(thm)], [f_184])).
% 8.67/3.12  tff(c_8905, plain, (![A_928, B_929]: (k2_relset_1(A_928, B_929, '#skF_4')=k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_8419, c_8901])).
% 8.67/3.12  tff(c_8917, plain, (![A_928, B_929]: (k2_relset_1(A_928, B_929, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8424, c_8905])).
% 8.67/3.12  tff(c_8919, plain, (k2_struct_0('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8917, c_244])).
% 8.67/3.12  tff(c_8928, plain, (v1_funct_2('#skF_4', k2_struct_0('#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8919, c_221])).
% 8.67/3.12  tff(c_183, plain, (![A_110]: (v1_xboole_0(k4_relat_1(A_110)) | ~v1_xboole_0(A_110))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.67/3.12  tff(c_187, plain, (![A_110]: (k4_relat_1(A_110)=k1_xboole_0 | ~v1_xboole_0(A_110))), inference(resolution, [status(thm)], [c_183, c_2])).
% 8.67/3.12  tff(c_8405, plain, (k4_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_8385, c_187])).
% 8.67/3.12  tff(c_8454, plain, (k4_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8406, c_8405])).
% 8.67/3.12  tff(c_8455, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8454, c_1195])).
% 8.67/3.12  tff(c_9619, plain, (![A_1035, B_1036, C_1037]: (k2_tops_2(A_1035, B_1036, C_1037)=k2_funct_1(C_1037) | ~v2_funct_1(C_1037) | k2_relset_1(A_1035, B_1036, C_1037)!=B_1036 | ~m1_subset_1(C_1037, k1_zfmisc_1(k2_zfmisc_1(A_1035, B_1036))) | ~v1_funct_2(C_1037, A_1035, B_1036) | ~v1_funct_1(C_1037))), inference(cnfTransformation, [status(thm)], [f_233])).
% 8.67/3.12  tff(c_9631, plain, (![A_1035, B_1036]: (k2_tops_2(A_1035, B_1036, '#skF_4')=k2_funct_1('#skF_4') | ~v2_funct_1('#skF_4') | k2_relset_1(A_1035, B_1036, '#skF_4')!=B_1036 | ~v1_funct_2('#skF_4', A_1035, B_1036) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_8419, c_9619])).
% 8.67/3.12  tff(c_9649, plain, (![A_1038, B_1039]: (k2_tops_2(A_1038, B_1039, '#skF_4')='#skF_4' | B_1039!='#skF_4' | ~v1_funct_2('#skF_4', A_1038, B_1039))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_8917, c_110, c_8455, c_9631])).
% 8.67/3.12  tff(c_9653, plain, (k2_tops_2(k2_struct_0('#skF_2'), '#skF_4', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_8928, c_9649])).
% 8.67/3.12  tff(c_1095, plain, (![A_240]: (v4_relat_1(k1_xboole_0, A_240))), inference(resolution, [status(thm)], [c_32, c_1074])).
% 8.67/3.12  tff(c_1098, plain, (![A_240]: (k7_relat_1(k1_xboole_0, A_240)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_1095, c_54])).
% 8.67/3.12  tff(c_1130, plain, (![A_244]: (k7_relat_1(k1_xboole_0, A_244)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1098])).
% 8.67/3.12  tff(c_1135, plain, (![A_244]: (k9_relat_1(k1_xboole_0, A_244)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1130, c_48])).
% 8.67/3.12  tff(c_1140, plain, (![A_244]: (k9_relat_1(k1_xboole_0, A_244)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_78, c_58, c_1135])).
% 8.67/3.12  tff(c_8410, plain, (![A_244]: (k9_relat_1('#skF_4', A_244)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8406, c_8406, c_1140])).
% 8.67/3.12  tff(c_9212, plain, (![A_976, B_977, C_978, D_979]: (k7_relset_1(A_976, B_977, C_978, D_979)=k9_relat_1(C_978, D_979) | ~m1_subset_1(C_978, k1_zfmisc_1(k2_zfmisc_1(A_976, B_977))))), inference(cnfTransformation, [status(thm)], [f_188])).
% 8.67/3.12  tff(c_9215, plain, (![A_976, B_977, D_979]: (k7_relset_1(A_976, B_977, '#skF_4', D_979)=k9_relat_1('#skF_4', D_979))), inference(resolution, [status(thm)], [c_8419, c_9212])).
% 8.67/3.12  tff(c_9224, plain, (![A_976, B_977, D_979]: (k7_relset_1(A_976, B_977, '#skF_4', D_979)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8410, c_9215])).
% 8.67/3.12  tff(c_8927, plain, (k8_relset_1('#skF_4', k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), '#skF_4', '#skF_4'), '#skF_5')!=k7_relset_1(k2_struct_0('#skF_2'), '#skF_4', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8919, c_8919, c_8919, c_1062])).
% 8.67/3.12  tff(c_9226, plain, (k8_relset_1('#skF_4', k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), '#skF_4', '#skF_4'), '#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9224, c_8927])).
% 8.67/3.12  tff(c_9654, plain, (k8_relset_1('#skF_4', k2_struct_0('#skF_2'), '#skF_4', '#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9653, c_9226])).
% 8.67/3.12  tff(c_9657, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9187, c_9654])).
% 8.67/3.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.67/3.12  
% 8.67/3.12  Inference rules
% 8.67/3.12  ----------------------
% 8.67/3.12  #Ref     : 0
% 8.67/3.12  #Sup     : 2171
% 8.67/3.12  #Fact    : 0
% 8.67/3.12  #Define  : 0
% 8.67/3.12  #Split   : 9
% 8.67/3.12  #Chain   : 0
% 8.67/3.12  #Close   : 0
% 8.67/3.12  
% 8.67/3.12  Ordering : KBO
% 8.67/3.12  
% 8.67/3.12  Simplification rules
% 8.67/3.12  ----------------------
% 8.67/3.12  #Subsume      : 243
% 8.67/3.12  #Demod        : 1870
% 8.67/3.12  #Tautology    : 798
% 8.67/3.12  #SimpNegUnit  : 14
% 8.67/3.12  #BackRed      : 85
% 8.67/3.12  
% 8.67/3.12  #Partial instantiations: 0
% 8.67/3.12  #Strategies tried      : 1
% 8.67/3.12  
% 8.67/3.12  Timing (in seconds)
% 8.67/3.12  ----------------------
% 8.67/3.13  Preprocessing        : 0.41
% 8.67/3.13  Parsing              : 0.22
% 8.67/3.13  CNF conversion       : 0.03
% 8.67/3.13  Main loop            : 1.90
% 8.67/3.13  Inferencing          : 0.63
% 8.67/3.13  Reduction            : 0.64
% 8.67/3.13  Demodulation         : 0.47
% 8.67/3.13  BG Simplification    : 0.08
% 8.67/3.13  Subsumption          : 0.39
% 8.67/3.13  Abstraction          : 0.09
% 8.67/3.13  MUC search           : 0.00
% 8.67/3.13  Cooper               : 0.00
% 8.67/3.13  Total                : 2.39
% 8.67/3.13  Index Insertion      : 0.00
% 8.67/3.13  Index Deletion       : 0.00
% 8.67/3.13  Index Matching       : 0.00
% 8.67/3.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
