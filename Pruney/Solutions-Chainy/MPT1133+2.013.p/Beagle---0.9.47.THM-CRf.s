%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:13 EST 2020

% Result     : Theorem 18.73s
% Output     : CNFRefutation 19.24s
% Verified   : 
% Statistics : Number of formulae       :  769 (67244 expanded)
%              Number of leaves         :   47 (21564 expanded)
%              Depth                    :   23
%              Number of atoms          : 2293 (246308 expanded)
%              Number of equality atoms :  315 (48444 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_relat_1 > v1_pre_topc > v1_funct_1 > l1_pre_topc > k1_relset_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_217,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ! [D] :
                    ( ( v1_funct_1(D)
                      & v1_funct_2(D,u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))),u1_struct_0(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))))
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))),u1_struct_0(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)))))) )
                   => ( C = D
                     => ( v5_pre_topc(C,A,B)
                      <=> v5_pre_topc(D,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)),g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_pre_topc)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_103,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_111,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_52,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_129,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).

tff(f_121,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_117,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v1_pre_topc(g1_pre_topc(A,B))
        & l1_pre_topc(g1_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

tff(f_158,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( ( v1_funct_1(D)
                    & v1_funct_2(D,u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))),u1_struct_0(B))
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))),u1_struct_0(B)))) )
                 => ( C = D
                   => ( v5_pre_topc(C,A,B)
                    <=> v5_pre_topc(D,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)),B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_pre_topc)).

tff(f_187,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( ( v1_funct_1(D)
                    & v1_funct_2(D,u1_struct_0(A),u1_struct_0(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))))
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)))))) )
                 => ( C = D
                   => ( v5_pre_topc(C,A,B)
                    <=> v5_pre_topc(D,A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_pre_topc)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_funct_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_funct_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_153,plain,(
    ! [A_83,B_84] :
      ( r1_tarski(A_83,B_84)
      | ~ m1_subset_1(A_83,k1_zfmisc_1(B_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_161,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(resolution,[status(thm)],[c_14,c_153])).

tff(c_74,plain,(
    '#skF_3' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_82,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_107,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_82])).

tff(c_197,plain,(
    ! [C_89,A_90,B_91] :
      ( v1_relat_1(C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_216,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_107,c_197])).

tff(c_84,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_103,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_84])).

tff(c_30559,plain,(
    ! [A_2122,B_2123,C_2124] :
      ( k1_relset_1(A_2122,B_2123,C_2124) = k1_relat_1(C_2124)
      | ~ m1_subset_1(C_2124,k1_zfmisc_1(k2_zfmisc_1(A_2122,B_2123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_30580,plain,(
    k1_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_107,c_30559])).

tff(c_31019,plain,(
    ! [B_2184,A_2185,C_2186] :
      ( k1_xboole_0 = B_2184
      | k1_relset_1(A_2185,B_2184,C_2186) = A_2185
      | ~ v1_funct_2(C_2186,A_2185,B_2184)
      | ~ m1_subset_1(C_2186,k1_zfmisc_1(k2_zfmisc_1(A_2185,B_2184))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_31025,plain,
    ( u1_struct_0('#skF_2') = k1_xboole_0
    | k1_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4') = u1_struct_0('#skF_1')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_107,c_31019])).

tff(c_31042,plain,
    ( u1_struct_0('#skF_2') = k1_xboole_0
    | u1_struct_0('#skF_1') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_30580,c_31025])).

tff(c_31047,plain,(
    u1_struct_0('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_31042])).

tff(c_383,plain,(
    ! [C_117,A_118,B_119] :
      ( v4_relat_1(C_117,A_118)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_404,plain,(
    v4_relat_1('#skF_4',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_107,c_383])).

tff(c_31058,plain,(
    v4_relat_1('#skF_4',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31047,c_404])).

tff(c_52,plain,(
    ! [B_30] :
      ( v1_partfun1(B_30,k1_relat_1(B_30))
      | ~ v4_relat_1(B_30,k1_relat_1(B_30))
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_31112,plain,
    ( v1_partfun1('#skF_4',k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_31058,c_52])).

tff(c_31119,plain,(
    v1_partfun1('#skF_4',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_31112])).

tff(c_27605,plain,(
    ! [B_1899,A_1900] :
      ( k1_relat_1(B_1899) = A_1900
      | ~ v1_partfun1(B_1899,A_1900)
      | ~ v4_relat_1(B_1899,A_1900)
      | ~ v1_relat_1(B_1899) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_27617,plain,
    ( u1_struct_0('#skF_1') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',u1_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_404,c_27605])).

tff(c_27630,plain,
    ( u1_struct_0('#skF_1') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_27617])).

tff(c_27647,plain,(
    ~ v1_partfun1('#skF_4',u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_27630])).

tff(c_31054,plain,(
    ~ v1_partfun1('#skF_4',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31047,c_27647])).

tff(c_31128,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_31119,c_31054])).

tff(c_31129,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_31042])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_193,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_107,c_16])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_196,plain,
    ( k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_193,c_2])).

tff(c_30729,plain,(
    ~ r1_tarski(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_196])).

tff(c_31134,plain,(
    ~ r1_tarski(k2_zfmisc_1(u1_struct_0('#skF_1'),k1_xboole_0),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31129,c_30729])).

tff(c_31147,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_10,c_31134])).

tff(c_31148,plain,(
    k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_31191,plain,
    ( u1_struct_0('#skF_2') = k1_xboole_0
    | u1_struct_0('#skF_1') = k1_xboole_0
    | k1_xboole_0 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_31148,c_8])).

tff(c_31405,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_31191])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_30661,plain,(
    ! [A_2138,B_2139,A_2140] :
      ( k1_relset_1(A_2138,B_2139,A_2140) = k1_relat_1(A_2140)
      | ~ r1_tarski(A_2140,k2_zfmisc_1(A_2138,B_2139)) ) ),
    inference(resolution,[status(thm)],[c_18,c_30559])).

tff(c_30688,plain,(
    ! [A_2138,B_2139] : k1_relset_1(A_2138,B_2139,k2_zfmisc_1(A_2138,B_2139)) = k1_relat_1(k2_zfmisc_1(A_2138,B_2139)) ),
    inference(resolution,[status(thm)],[c_6,c_30661])).

tff(c_31346,plain,(
    ! [B_2196,A_2197,C_2198] :
      ( k1_xboole_0 = B_2196
      | k1_relset_1(A_2197,B_2196,C_2198) = A_2197
      | ~ v1_funct_2(C_2198,A_2197,B_2196)
      | ~ m1_subset_1(C_2198,k1_zfmisc_1(k2_zfmisc_1(A_2197,B_2196))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_31823,plain,(
    ! [B_2246,A_2247,A_2248] :
      ( k1_xboole_0 = B_2246
      | k1_relset_1(A_2247,B_2246,A_2248) = A_2247
      | ~ v1_funct_2(A_2248,A_2247,B_2246)
      | ~ r1_tarski(A_2248,k2_zfmisc_1(A_2247,B_2246)) ) ),
    inference(resolution,[status(thm)],[c_18,c_31346])).

tff(c_31843,plain,(
    ! [B_2246,A_2247] :
      ( k1_xboole_0 = B_2246
      | k1_relset_1(A_2247,B_2246,k2_zfmisc_1(A_2247,B_2246)) = A_2247
      | ~ v1_funct_2(k2_zfmisc_1(A_2247,B_2246),A_2247,B_2246) ) ),
    inference(resolution,[status(thm)],[c_6,c_31823])).

tff(c_31849,plain,(
    ! [B_2249,A_2250] :
      ( k1_xboole_0 = B_2249
      | k1_relat_1(k2_zfmisc_1(A_2250,B_2249)) = A_2250
      | ~ v1_funct_2(k2_zfmisc_1(A_2250,B_2249),A_2250,B_2249) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30688,c_31843])).

tff(c_31873,plain,
    ( u1_struct_0('#skF_2') = k1_xboole_0
    | k1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))) = u1_struct_0('#skF_1')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_31148,c_31849])).

tff(c_31898,plain,
    ( u1_struct_0('#skF_2') = k1_xboole_0
    | u1_struct_0('#skF_1') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_31148,c_31873])).

tff(c_31905,plain,(
    u1_struct_0('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_31898])).

tff(c_31921,plain,(
    ~ v1_partfun1('#skF_4',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31905,c_27647])).

tff(c_31924,plain,(
    v4_relat_1('#skF_4',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31905,c_404])).

tff(c_32019,plain,
    ( v1_partfun1('#skF_4',k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_31924,c_52])).

tff(c_32026,plain,(
    v1_partfun1('#skF_4',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_32019])).

tff(c_32033,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_31921,c_32026])).

tff(c_32034,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_31898])).

tff(c_32045,plain,(
    k2_zfmisc_1(u1_struct_0('#skF_1'),k1_xboole_0) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32034,c_31148])).

tff(c_32185,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_32045,c_10])).

tff(c_32206,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_31405,c_32185])).

tff(c_32208,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_31191])).

tff(c_219,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_197])).

tff(c_407,plain,(
    ! [A_118] : v4_relat_1(k1_xboole_0,A_118) ),
    inference(resolution,[status(thm)],[c_14,c_383])).

tff(c_24,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_27490,plain,(
    ! [B_1881] :
      ( v1_partfun1(B_1881,k1_relat_1(B_1881))
      | ~ v4_relat_1(B_1881,k1_relat_1(B_1881))
      | ~ v1_relat_1(B_1881) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_27501,plain,
    ( v1_partfun1(k1_xboole_0,k1_relat_1(k1_xboole_0))
    | ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_27490])).

tff(c_27507,plain,(
    v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_407,c_24,c_27501])).

tff(c_32253,plain,(
    v1_partfun1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32208,c_32208,c_27507])).

tff(c_90,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_88,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_32207,plain,
    ( u1_struct_0('#skF_1') = k1_xboole_0
    | u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_31191])).

tff(c_34443,plain,
    ( u1_struct_0('#skF_1') = '#skF_4'
    | u1_struct_0('#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32208,c_32208,c_32207])).

tff(c_34444,plain,(
    u1_struct_0('#skF_2') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_34443])).

tff(c_34448,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34444,c_103])).

tff(c_102,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_104,plain,
    ( v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_102])).

tff(c_489,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_104])).

tff(c_96,plain,
    ( ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_106,plain,
    ( ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_96])).

tff(c_551,plain,(
    ~ v5_pre_topc('#skF_4','#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_62,plain,(
    ! [A_34] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(A_34),u1_pre_topc(A_34)))
      | ~ l1_pre_topc(A_34)
      | ~ v2_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_466,plain,(
    ! [A_132] :
      ( m1_subset_1(u1_pre_topc(A_132),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_132))))
      | ~ l1_pre_topc(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_56,plain,(
    ! [A_31,B_32] :
      ( l1_pre_topc(g1_pre_topc(A_31,B_32))
      | ~ m1_subset_1(B_32,k1_zfmisc_1(k1_zfmisc_1(A_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_473,plain,(
    ! [A_132] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_132),u1_pre_topc(A_132)))
      | ~ l1_pre_topc(A_132) ) ),
    inference(resolution,[status(thm)],[c_466,c_56])).

tff(c_80,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_733,plain,(
    ! [A_176,B_177,C_178] :
      ( k1_relset_1(A_176,B_177,C_178) = k1_relat_1(C_178)
      | ~ m1_subset_1(C_178,k1_zfmisc_1(k2_zfmisc_1(A_176,B_177))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_754,plain,(
    k1_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_107,c_733])).

tff(c_3647,plain,(
    ! [B_409,A_410,C_411] :
      ( k1_xboole_0 = B_409
      | k1_relset_1(A_410,B_409,C_411) = A_410
      | ~ v1_funct_2(C_411,A_410,B_409)
      | ~ m1_subset_1(C_411,k1_zfmisc_1(k2_zfmisc_1(A_410,B_409))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_3653,plain,
    ( u1_struct_0('#skF_2') = k1_xboole_0
    | k1_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4') = u1_struct_0('#skF_1')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_107,c_3647])).

tff(c_3670,plain,
    ( u1_struct_0('#skF_2') = k1_xboole_0
    | u1_struct_0('#skF_1') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_754,c_3653])).

tff(c_3675,plain,(
    u1_struct_0('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3670])).

tff(c_3686,plain,(
    v4_relat_1('#skF_4',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3675,c_404])).

tff(c_3740,plain,
    ( v1_partfun1('#skF_4',k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_3686,c_52])).

tff(c_3747,plain,(
    v1_partfun1('#skF_4',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_3740])).

tff(c_647,plain,(
    ! [B_162,A_163] :
      ( k1_relat_1(B_162) = A_163
      | ~ v1_partfun1(B_162,A_163)
      | ~ v4_relat_1(B_162,A_163)
      | ~ v1_relat_1(B_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_659,plain,
    ( u1_struct_0('#skF_1') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',u1_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_404,c_647])).

tff(c_672,plain,
    ( u1_struct_0('#skF_1') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_659])).

tff(c_689,plain,(
    ~ v1_partfun1('#skF_4',u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_672])).

tff(c_3682,plain,(
    ~ v1_partfun1('#skF_4',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3675,c_689])).

tff(c_3756,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3747,c_3682])).

tff(c_3757,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_3670])).

tff(c_3378,plain,(
    ~ r1_tarski(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_196])).

tff(c_3762,plain,(
    ~ r1_tarski(k2_zfmisc_1(u1_struct_0('#skF_1'),k1_xboole_0),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3757,c_3378])).

tff(c_3775,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_10,c_3762])).

tff(c_3776,plain,(
    k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_3819,plain,
    ( u1_struct_0('#skF_2') = k1_xboole_0
    | u1_struct_0('#skF_1') = k1_xboole_0
    | k1_xboole_0 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_3776,c_8])).

tff(c_4034,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3819])).

tff(c_816,plain,(
    ! [A_189,B_190,A_191] :
      ( k1_relset_1(A_189,B_190,A_191) = k1_relat_1(A_191)
      | ~ r1_tarski(A_191,k2_zfmisc_1(A_189,B_190)) ) ),
    inference(resolution,[status(thm)],[c_18,c_733])).

tff(c_843,plain,(
    ! [A_189,B_190] : k1_relset_1(A_189,B_190,k2_zfmisc_1(A_189,B_190)) = k1_relat_1(k2_zfmisc_1(A_189,B_190)) ),
    inference(resolution,[status(thm)],[c_6,c_816])).

tff(c_3978,plain,(
    ! [B_421,A_422,C_423] :
      ( k1_xboole_0 = B_421
      | k1_relset_1(A_422,B_421,C_423) = A_422
      | ~ v1_funct_2(C_423,A_422,B_421)
      | ~ m1_subset_1(C_423,k1_zfmisc_1(k2_zfmisc_1(A_422,B_421))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_4395,plain,(
    ! [B_469,A_470,A_471] :
      ( k1_xboole_0 = B_469
      | k1_relset_1(A_470,B_469,A_471) = A_470
      | ~ v1_funct_2(A_471,A_470,B_469)
      | ~ r1_tarski(A_471,k2_zfmisc_1(A_470,B_469)) ) ),
    inference(resolution,[status(thm)],[c_18,c_3978])).

tff(c_4415,plain,(
    ! [B_469,A_470] :
      ( k1_xboole_0 = B_469
      | k1_relset_1(A_470,B_469,k2_zfmisc_1(A_470,B_469)) = A_470
      | ~ v1_funct_2(k2_zfmisc_1(A_470,B_469),A_470,B_469) ) ),
    inference(resolution,[status(thm)],[c_6,c_4395])).

tff(c_4421,plain,(
    ! [B_472,A_473] :
      ( k1_xboole_0 = B_472
      | k1_relat_1(k2_zfmisc_1(A_473,B_472)) = A_473
      | ~ v1_funct_2(k2_zfmisc_1(A_473,B_472),A_473,B_472) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_843,c_4415])).

tff(c_4442,plain,
    ( u1_struct_0('#skF_2') = k1_xboole_0
    | k1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))) = u1_struct_0('#skF_1')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3776,c_4421])).

tff(c_4466,plain,
    ( u1_struct_0('#skF_2') = k1_xboole_0
    | u1_struct_0('#skF_1') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_3776,c_4442])).

tff(c_4473,plain,(
    u1_struct_0('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_4466])).

tff(c_4489,plain,(
    ~ v1_partfun1('#skF_4',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4473,c_689])).

tff(c_4492,plain,(
    v4_relat_1('#skF_4',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4473,c_404])).

tff(c_4564,plain,
    ( v1_partfun1('#skF_4',k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_4492,c_52])).

tff(c_4571,plain,(
    v1_partfun1('#skF_4',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_4564])).

tff(c_4601,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4489,c_4571])).

tff(c_4602,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_4466])).

tff(c_4667,plain,(
    k2_zfmisc_1(u1_struct_0('#skF_1'),k1_xboole_0) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4602,c_3776])).

tff(c_4801,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_4667,c_10])).

tff(c_4819,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4034,c_4801])).

tff(c_4821,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3819])).

tff(c_533,plain,(
    ! [B_146] :
      ( v1_partfun1(B_146,k1_relat_1(B_146))
      | ~ v4_relat_1(B_146,k1_relat_1(B_146))
      | ~ v1_relat_1(B_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_544,plain,
    ( v1_partfun1(k1_xboole_0,k1_relat_1(k1_xboole_0))
    | ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_533])).

tff(c_550,plain,(
    v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_407,c_24,c_544])).

tff(c_4840,plain,(
    v1_partfun1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4821,c_4821,c_550])).

tff(c_4820,plain,
    ( u1_struct_0('#skF_1') = k1_xboole_0
    | u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_3819])).

tff(c_6658,plain,
    ( u1_struct_0('#skF_1') = '#skF_4'
    | u1_struct_0('#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4821,c_4821,c_4820])).

tff(c_6659,plain,(
    u1_struct_0('#skF_2') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_6658])).

tff(c_6666,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6659,c_103])).

tff(c_6665,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6659,c_489])).

tff(c_12,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4857,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_4',B_4) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4821,c_4821,c_12])).

tff(c_94,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_92,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_5256,plain,
    ( u1_struct_0('#skF_1') = '#skF_4'
    | u1_struct_0('#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4821,c_4821,c_4820])).

tff(c_5257,plain,(
    u1_struct_0('#skF_2') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_5256])).

tff(c_5263,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5257,c_103])).

tff(c_4856,plain,(
    ! [A_5] : m1_subset_1('#skF_4',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4821,c_14])).

tff(c_78,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_5264,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5257,c_78])).

tff(c_747,plain,(
    ! [A_176,B_177] : k1_relset_1(A_176,B_177,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_733])).

tff(c_758,plain,(
    ! [A_176,B_177] : k1_relset_1(A_176,B_177,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_747])).

tff(c_3992,plain,(
    ! [B_421,A_422] :
      ( k1_xboole_0 = B_421
      | k1_relset_1(A_422,B_421,k1_xboole_0) = A_422
      | ~ v1_funct_2(k1_xboole_0,A_422,B_421) ) ),
    inference(resolution,[status(thm)],[c_14,c_3978])).

tff(c_4001,plain,(
    ! [B_421,A_422] :
      ( k1_xboole_0 = B_421
      | k1_xboole_0 = A_422
      | ~ v1_funct_2(k1_xboole_0,A_422,B_421) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_758,c_3992])).

tff(c_5475,plain,(
    ! [B_527,A_528] :
      ( B_527 = '#skF_4'
      | A_528 = '#skF_4'
      | ~ v1_funct_2('#skF_4',A_528,B_527) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4821,c_4821,c_4821,c_4001])).

tff(c_5494,plain,
    ( u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) = '#skF_4'
    | u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5264,c_5475])).

tff(c_5510,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_5494])).

tff(c_4859,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4821,c_4821,c_24])).

tff(c_76,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_405,plain,(
    v4_relat_1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(resolution,[status(thm)],[c_76,c_383])).

tff(c_656,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_405,c_647])).

tff(c_669,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_656])).

tff(c_5221,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = '#skF_4'
    | ~ v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4859,c_669])).

tff(c_5222,plain,(
    ~ v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(splitLeft,[status(thm)],[c_5221])).

tff(c_5511,plain,(
    ~ v1_partfun1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5510,c_5222])).

tff(c_5515,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4840,c_5511])).

tff(c_5516,plain,(
    u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5494])).

tff(c_5518,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5516,c_5264])).

tff(c_5262,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5257,c_489])).

tff(c_5293,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5257,c_62])).

tff(c_5325,plain,(
    v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_5293])).

tff(c_5302,plain,
    ( l1_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5257,c_473])).

tff(c_5331,plain,(
    l1_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_5302])).

tff(c_4858,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4821,c_4821,c_10])).

tff(c_1020,plain,(
    ! [B_224,A_225,C_226] :
      ( k1_xboole_0 = B_224
      | k1_relset_1(A_225,B_224,C_226) = A_225
      | ~ v1_funct_2(C_226,A_225,B_224)
      | ~ m1_subset_1(C_226,k1_zfmisc_1(k2_zfmisc_1(A_225,B_224))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1023,plain,
    ( u1_struct_0('#skF_2') = k1_xboole_0
    | k1_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4') = u1_struct_0('#skF_1')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_107,c_1020])).

tff(c_1043,plain,
    ( u1_struct_0('#skF_2') = k1_xboole_0
    | u1_struct_0('#skF_1') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_754,c_1023])).

tff(c_1051,plain,(
    u1_struct_0('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1043])).

tff(c_1061,plain,(
    v4_relat_1('#skF_4',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1051,c_404])).

tff(c_1117,plain,
    ( v1_partfun1('#skF_4',k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1061,c_52])).

tff(c_1124,plain,(
    v1_partfun1('#skF_4',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_1117])).

tff(c_1057,plain,(
    ~ v1_partfun1('#skF_4',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1051,c_689])).

tff(c_1133,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1124,c_1057])).

tff(c_1134,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1043])).

tff(c_904,plain,(
    ~ r1_tarski(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_196])).

tff(c_1137,plain,(
    ~ r1_tarski(k2_zfmisc_1(u1_struct_0('#skF_1'),k1_xboole_0),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1134,c_904])).

tff(c_1153,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_10,c_1137])).

tff(c_1154,plain,(
    k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_1197,plain,
    ( u1_struct_0('#skF_2') = k1_xboole_0
    | u1_struct_0('#skF_1') = k1_xboole_0
    | k1_xboole_0 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1154,c_8])).

tff(c_1718,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1197])).

tff(c_755,plain,(
    k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_733])).

tff(c_1449,plain,(
    ! [B_246,A_247,C_248] :
      ( k1_xboole_0 = B_246
      | k1_relset_1(A_247,B_246,C_248) = A_247
      | ~ v1_funct_2(C_248,A_247,B_246)
      | ~ m1_subset_1(C_248,k1_zfmisc_1(k2_zfmisc_1(A_247,B_246))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1455,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0
    | k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') = u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(resolution,[status(thm)],[c_76,c_1449])).

tff(c_1472,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_755,c_1455])).

tff(c_1531,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1472])).

tff(c_1536,plain,(
    v4_relat_1('#skF_4',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1531,c_405])).

tff(c_1571,plain,
    ( v1_partfun1('#skF_4',k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1536,c_52])).

tff(c_1578,plain,(
    v1_partfun1('#skF_4',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_1571])).

tff(c_1349,plain,(
    ~ v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(splitLeft,[status(thm)],[c_669])).

tff(c_1532,plain,(
    ~ v1_partfun1('#skF_4',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1531,c_1349])).

tff(c_1587,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1578,c_1532])).

tff(c_1588,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1472])).

tff(c_176,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))) ),
    inference(resolution,[status(thm)],[c_76,c_16])).

tff(c_246,plain,
    ( k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))),'#skF_4') ),
    inference(resolution,[status(thm)],[c_176,c_2])).

tff(c_901,plain,(
    ~ r1_tarski(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_246])).

tff(c_1590,plain,(
    ~ r1_tarski(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),k1_xboole_0),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1588,c_901])).

tff(c_1599,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_10,c_1590])).

tff(c_1600,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_669])).

tff(c_1601,plain,(
    v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_669])).

tff(c_1663,plain,(
    v1_partfun1('#skF_4',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1600,c_1601])).

tff(c_1602,plain,(
    ! [B_255,A_256,C_257] :
      ( k1_xboole_0 = B_255
      | k1_relset_1(A_256,B_255,C_257) = A_256
      | ~ v1_funct_2(C_257,A_256,B_255)
      | ~ m1_subset_1(C_257,k1_zfmisc_1(k2_zfmisc_1(A_256,B_255))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2107,plain,(
    ! [B_291,A_292,A_293] :
      ( k1_xboole_0 = B_291
      | k1_relset_1(A_292,B_291,A_293) = A_292
      | ~ v1_funct_2(A_293,A_292,B_291)
      | ~ r1_tarski(A_293,k2_zfmisc_1(A_292,B_291)) ) ),
    inference(resolution,[status(thm)],[c_18,c_1602])).

tff(c_2127,plain,(
    ! [B_291,A_292] :
      ( k1_xboole_0 = B_291
      | k1_relset_1(A_292,B_291,k2_zfmisc_1(A_292,B_291)) = A_292
      | ~ v1_funct_2(k2_zfmisc_1(A_292,B_291),A_292,B_291) ) ),
    inference(resolution,[status(thm)],[c_6,c_2107])).

tff(c_2136,plain,(
    ! [B_294,A_295] :
      ( k1_xboole_0 = B_294
      | k1_relat_1(k2_zfmisc_1(A_295,B_294)) = A_295
      | ~ v1_funct_2(k2_zfmisc_1(A_295,B_294),A_295,B_294) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_843,c_2127])).

tff(c_2154,plain,
    ( u1_struct_0('#skF_2') = k1_xboole_0
    | k1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))) = u1_struct_0('#skF_1')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1154,c_2136])).

tff(c_2176,plain,
    ( u1_struct_0('#skF_2') = k1_xboole_0
    | u1_struct_0('#skF_1') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_1154,c_2154])).

tff(c_2183,plain,(
    u1_struct_0('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2176])).

tff(c_2220,plain,(
    ~ v1_partfun1('#skF_4',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2183,c_689])).

tff(c_2226,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1663,c_2220])).

tff(c_2227,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2176])).

tff(c_2240,plain,(
    k2_zfmisc_1(u1_struct_0('#skF_1'),k1_xboole_0) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2227,c_1154])).

tff(c_2387,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2240,c_10])).

tff(c_2406,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1718,c_2387])).

tff(c_2408,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1197])).

tff(c_2446,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_4',B_4) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2408,c_2408,c_12])).

tff(c_2448,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2408,c_2408,c_24])).

tff(c_1664,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1600,c_901])).

tff(c_3374,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2446,c_2448,c_1664])).

tff(c_3375,plain,(
    k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_246])).

tff(c_5230,plain,(
    ! [D_500,A_501,B_502] :
      ( v5_pre_topc(D_500,A_501,B_502)
      | ~ v5_pre_topc(D_500,g1_pre_topc(u1_struct_0(A_501),u1_pre_topc(A_501)),B_502)
      | ~ m1_subset_1(D_500,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_501),u1_pre_topc(A_501))),u1_struct_0(B_502))))
      | ~ v1_funct_2(D_500,u1_struct_0(g1_pre_topc(u1_struct_0(A_501),u1_pre_topc(A_501))),u1_struct_0(B_502))
      | ~ m1_subset_1(D_500,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_501),u1_struct_0(B_502))))
      | ~ v1_funct_2(D_500,u1_struct_0(A_501),u1_struct_0(B_502))
      | ~ v1_funct_1(D_500)
      | ~ l1_pre_topc(B_502)
      | ~ v2_pre_topc(B_502)
      | ~ l1_pre_topc(A_501)
      | ~ v2_pre_topc(A_501) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_5237,plain,(
    ! [D_500] :
      ( v5_pre_topc(D_500,'#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc(D_500,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ m1_subset_1(D_500,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_2(D_500,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1(D_500,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))))
      | ~ v1_funct_2(D_500,u1_struct_0('#skF_1'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ v1_funct_1(D_500)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3375,c_5230])).

tff(c_5246,plain,(
    ! [D_500] :
      ( v5_pre_topc(D_500,'#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc(D_500,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ m1_subset_1(D_500,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_2(D_500,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1(D_500,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))))
      | ~ v1_funct_2(D_500,u1_struct_0('#skF_1'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ v1_funct_1(D_500)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_5237])).

tff(c_6585,plain,(
    ! [D_618] :
      ( v5_pre_topc(D_618,'#skF_1',g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc(D_618,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v1_funct_2(D_618,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4')
      | ~ m1_subset_1(D_618,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_2(D_618,u1_struct_0('#skF_1'),'#skF_4')
      | ~ v1_funct_1(D_618) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5325,c_5257,c_5331,c_5257,c_5516,c_5257,c_4858,c_5516,c_5257,c_5516,c_5257,c_5257,c_5257,c_5246])).

tff(c_6592,plain,
    ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4'))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_5262,c_6585])).

tff(c_6598,plain,(
    v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_5263,c_4856,c_5518,c_6592])).

tff(c_5335,plain,(
    ! [D_504,A_505,B_506] :
      ( v5_pre_topc(D_504,A_505,B_506)
      | ~ v5_pre_topc(D_504,A_505,g1_pre_topc(u1_struct_0(B_506),u1_pre_topc(B_506)))
      | ~ m1_subset_1(D_504,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_505),u1_struct_0(g1_pre_topc(u1_struct_0(B_506),u1_pre_topc(B_506))))))
      | ~ v1_funct_2(D_504,u1_struct_0(A_505),u1_struct_0(g1_pre_topc(u1_struct_0(B_506),u1_pre_topc(B_506))))
      | ~ m1_subset_1(D_504,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_505),u1_struct_0(B_506))))
      | ~ v1_funct_2(D_504,u1_struct_0(A_505),u1_struct_0(B_506))
      | ~ v1_funct_1(D_504)
      | ~ l1_pre_topc(B_506)
      | ~ v2_pre_topc(B_506)
      | ~ l1_pre_topc(A_505)
      | ~ v2_pre_topc(A_505) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_5910,plain,(
    ! [A_564,A_565,B_566] :
      ( v5_pre_topc(A_564,A_565,B_566)
      | ~ v5_pre_topc(A_564,A_565,g1_pre_topc(u1_struct_0(B_566),u1_pre_topc(B_566)))
      | ~ v1_funct_2(A_564,u1_struct_0(A_565),u1_struct_0(g1_pre_topc(u1_struct_0(B_566),u1_pre_topc(B_566))))
      | ~ m1_subset_1(A_564,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_565),u1_struct_0(B_566))))
      | ~ v1_funct_2(A_564,u1_struct_0(A_565),u1_struct_0(B_566))
      | ~ v1_funct_1(A_564)
      | ~ l1_pre_topc(B_566)
      | ~ v2_pre_topc(B_566)
      | ~ l1_pre_topc(A_565)
      | ~ v2_pre_topc(A_565)
      | ~ r1_tarski(A_564,k2_zfmisc_1(u1_struct_0(A_565),u1_struct_0(g1_pre_topc(u1_struct_0(B_566),u1_pre_topc(B_566))))) ) ),
    inference(resolution,[status(thm)],[c_18,c_5335])).

tff(c_6456,plain,(
    ! [A_613,B_614] :
      ( v5_pre_topc(k2_zfmisc_1(u1_struct_0(A_613),u1_struct_0(g1_pre_topc(u1_struct_0(B_614),u1_pre_topc(B_614)))),A_613,B_614)
      | ~ v5_pre_topc(k2_zfmisc_1(u1_struct_0(A_613),u1_struct_0(g1_pre_topc(u1_struct_0(B_614),u1_pre_topc(B_614)))),A_613,g1_pre_topc(u1_struct_0(B_614),u1_pre_topc(B_614)))
      | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(A_613),u1_struct_0(g1_pre_topc(u1_struct_0(B_614),u1_pre_topc(B_614)))),u1_struct_0(A_613),u1_struct_0(g1_pre_topc(u1_struct_0(B_614),u1_pre_topc(B_614))))
      | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(A_613),u1_struct_0(g1_pre_topc(u1_struct_0(B_614),u1_pre_topc(B_614)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_613),u1_struct_0(B_614))))
      | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(A_613),u1_struct_0(g1_pre_topc(u1_struct_0(B_614),u1_pre_topc(B_614)))),u1_struct_0(A_613),u1_struct_0(B_614))
      | ~ v1_funct_1(k2_zfmisc_1(u1_struct_0(A_613),u1_struct_0(g1_pre_topc(u1_struct_0(B_614),u1_pre_topc(B_614)))))
      | ~ l1_pre_topc(B_614)
      | ~ v2_pre_topc(B_614)
      | ~ l1_pre_topc(A_613)
      | ~ v2_pre_topc(A_613) ) ),
    inference(resolution,[status(thm)],[c_6,c_5910])).

tff(c_6480,plain,(
    ! [A_613] :
      ( v5_pre_topc(k2_zfmisc_1(u1_struct_0(A_613),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))),A_613,'#skF_2')
      | ~ v5_pre_topc(k2_zfmisc_1(u1_struct_0(A_613),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))),A_613,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(A_613),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))),u1_struct_0(A_613),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(A_613),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_613),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(A_613),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))),u1_struct_0(A_613),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_zfmisc_1(u1_struct_0(A_613),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_613)
      | ~ v2_pre_topc(A_613) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5257,c_6456])).

tff(c_6500,plain,(
    ! [A_613] :
      ( v5_pre_topc('#skF_4',A_613,'#skF_2')
      | ~ v5_pre_topc('#skF_4',A_613,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_613),'#skF_4')
      | ~ l1_pre_topc(A_613)
      | ~ v2_pre_topc(A_613) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_80,c_4858,c_5516,c_5257,c_4858,c_5516,c_5257,c_5257,c_4856,c_4858,c_5516,c_4858,c_5257,c_5257,c_5516,c_4858,c_5516,c_5257,c_4858,c_5516,c_5257,c_5257,c_4858,c_5516,c_5257,c_6480])).

tff(c_6601,plain,
    ( v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_6598,c_6500])).

tff(c_6604,plain,(
    v5_pre_topc('#skF_4','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_5263,c_6601])).

tff(c_6606,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_551,c_6604])).

tff(c_6607,plain,(
    u1_struct_0('#skF_1') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5256])).

tff(c_6614,plain,(
    ~ v1_partfun1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6607,c_689])).

tff(c_6621,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4840,c_6614])).

tff(c_6622,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5221])).

tff(c_6914,plain,
    ( l1_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_6622,c_473])).

tff(c_7531,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_6914])).

tff(c_7534,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_473,c_7531])).

tff(c_7538,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_7534])).

tff(c_7540,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_6914])).

tff(c_6905,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_6622,c_62])).

tff(c_7906,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7540,c_6905])).

tff(c_7907,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_7906])).

tff(c_7910,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_7907])).

tff(c_7914,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_7910])).

tff(c_7916,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_7906])).

tff(c_44,plain,(
    ! [C_28,B_27] :
      ( v1_funct_2(C_28,k1_xboole_0,B_27)
      | k1_relset_1(k1_xboole_0,B_27,C_28) != k1_xboole_0
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_861,plain,(
    ! [C_194,B_195] :
      ( v1_funct_2(C_194,k1_xboole_0,B_195)
      | k1_relset_1(k1_xboole_0,B_195,C_194) != k1_xboole_0
      | ~ m1_subset_1(C_194,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_44])).

tff(c_867,plain,(
    ! [B_195] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_195)
      | k1_relset_1(k1_xboole_0,B_195,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14,c_861])).

tff(c_871,plain,(
    ! [B_195] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_195) ),
    inference(demodulation,[status(thm),theory(equality)],[c_758,c_867])).

tff(c_4827,plain,(
    ! [B_195] : v1_funct_2('#skF_4','#skF_4',B_195) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4821,c_4821,c_871])).

tff(c_3844,plain,(
    ! [C_412,A_413,B_414] :
      ( v1_funct_2(C_412,A_413,B_414)
      | ~ v1_partfun1(C_412,A_413)
      | ~ v1_funct_1(C_412)
      | ~ m1_subset_1(C_412,k1_zfmisc_1(k2_zfmisc_1(A_413,B_414))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_6939,plain,(
    ! [A_645,A_646,B_647] :
      ( v1_funct_2(A_645,A_646,B_647)
      | ~ v1_partfun1(A_645,A_646)
      | ~ v1_funct_1(A_645)
      | ~ r1_tarski(A_645,k2_zfmisc_1(A_646,B_647)) ) ),
    inference(resolution,[status(thm)],[c_18,c_3844])).

tff(c_6957,plain,(
    ! [A_646,B_647] :
      ( v1_funct_2(k2_zfmisc_1(A_646,B_647),A_646,B_647)
      | ~ v1_partfun1(k2_zfmisc_1(A_646,B_647),A_646)
      | ~ v1_funct_1(k2_zfmisc_1(A_646,B_647)) ) ),
    inference(resolution,[status(thm)],[c_6,c_6939])).

tff(c_6738,plain,(
    ! [D_625,A_626,B_627] :
      ( v5_pre_topc(D_625,A_626,B_627)
      | ~ v5_pre_topc(D_625,A_626,g1_pre_topc(u1_struct_0(B_627),u1_pre_topc(B_627)))
      | ~ m1_subset_1(D_625,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_626),u1_struct_0(g1_pre_topc(u1_struct_0(B_627),u1_pre_topc(B_627))))))
      | ~ v1_funct_2(D_625,u1_struct_0(A_626),u1_struct_0(g1_pre_topc(u1_struct_0(B_627),u1_pre_topc(B_627))))
      | ~ m1_subset_1(D_625,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_626),u1_struct_0(B_627))))
      | ~ v1_funct_2(D_625,u1_struct_0(A_626),u1_struct_0(B_627))
      | ~ v1_funct_1(D_625)
      | ~ l1_pre_topc(B_627)
      | ~ v2_pre_topc(B_627)
      | ~ l1_pre_topc(A_626)
      | ~ v2_pre_topc(A_626) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_7121,plain,(
    ! [A_670,A_671,B_672] :
      ( v5_pre_topc(A_670,A_671,B_672)
      | ~ v5_pre_topc(A_670,A_671,g1_pre_topc(u1_struct_0(B_672),u1_pre_topc(B_672)))
      | ~ v1_funct_2(A_670,u1_struct_0(A_671),u1_struct_0(g1_pre_topc(u1_struct_0(B_672),u1_pre_topc(B_672))))
      | ~ m1_subset_1(A_670,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_671),u1_struct_0(B_672))))
      | ~ v1_funct_2(A_670,u1_struct_0(A_671),u1_struct_0(B_672))
      | ~ v1_funct_1(A_670)
      | ~ l1_pre_topc(B_672)
      | ~ v2_pre_topc(B_672)
      | ~ l1_pre_topc(A_671)
      | ~ v2_pre_topc(A_671)
      | ~ r1_tarski(A_670,k2_zfmisc_1(u1_struct_0(A_671),u1_struct_0(g1_pre_topc(u1_struct_0(B_672),u1_pre_topc(B_672))))) ) ),
    inference(resolution,[status(thm)],[c_18,c_6738])).

tff(c_7478,plain,(
    ! [A_706,B_707] :
      ( v5_pre_topc(k2_zfmisc_1(u1_struct_0(A_706),u1_struct_0(g1_pre_topc(u1_struct_0(B_707),u1_pre_topc(B_707)))),A_706,B_707)
      | ~ v5_pre_topc(k2_zfmisc_1(u1_struct_0(A_706),u1_struct_0(g1_pre_topc(u1_struct_0(B_707),u1_pre_topc(B_707)))),A_706,g1_pre_topc(u1_struct_0(B_707),u1_pre_topc(B_707)))
      | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(A_706),u1_struct_0(g1_pre_topc(u1_struct_0(B_707),u1_pre_topc(B_707)))),u1_struct_0(A_706),u1_struct_0(g1_pre_topc(u1_struct_0(B_707),u1_pre_topc(B_707))))
      | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(A_706),u1_struct_0(g1_pre_topc(u1_struct_0(B_707),u1_pre_topc(B_707)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_706),u1_struct_0(B_707))))
      | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(A_706),u1_struct_0(g1_pre_topc(u1_struct_0(B_707),u1_pre_topc(B_707)))),u1_struct_0(A_706),u1_struct_0(B_707))
      | ~ v1_funct_1(k2_zfmisc_1(u1_struct_0(A_706),u1_struct_0(g1_pre_topc(u1_struct_0(B_707),u1_pre_topc(B_707)))))
      | ~ l1_pre_topc(B_707)
      | ~ v2_pre_topc(B_707)
      | ~ l1_pre_topc(A_706)
      | ~ v2_pre_topc(A_706) ) ),
    inference(resolution,[status(thm)],[c_6,c_7121])).

tff(c_8155,plain,(
    ! [A_742,B_743] :
      ( v5_pre_topc(k2_zfmisc_1(u1_struct_0(A_742),u1_struct_0(g1_pre_topc(u1_struct_0(B_743),u1_pre_topc(B_743)))),A_742,B_743)
      | ~ v5_pre_topc(k2_zfmisc_1(u1_struct_0(A_742),u1_struct_0(g1_pre_topc(u1_struct_0(B_743),u1_pre_topc(B_743)))),A_742,g1_pre_topc(u1_struct_0(B_743),u1_pre_topc(B_743)))
      | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(A_742),u1_struct_0(g1_pre_topc(u1_struct_0(B_743),u1_pre_topc(B_743)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_742),u1_struct_0(B_743))))
      | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(A_742),u1_struct_0(g1_pre_topc(u1_struct_0(B_743),u1_pre_topc(B_743)))),u1_struct_0(A_742),u1_struct_0(B_743))
      | ~ l1_pre_topc(B_743)
      | ~ v2_pre_topc(B_743)
      | ~ l1_pre_topc(A_742)
      | ~ v2_pre_topc(A_742)
      | ~ v1_partfun1(k2_zfmisc_1(u1_struct_0(A_742),u1_struct_0(g1_pre_topc(u1_struct_0(B_743),u1_pre_topc(B_743)))),u1_struct_0(A_742))
      | ~ v1_funct_1(k2_zfmisc_1(u1_struct_0(A_742),u1_struct_0(g1_pre_topc(u1_struct_0(B_743),u1_pre_topc(B_743))))) ) ),
    inference(resolution,[status(thm)],[c_6957,c_7478])).

tff(c_8157,plain,(
    ! [B_743] :
      ( v5_pre_topc(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0(B_743),u1_pre_topc(B_743)))),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_743)
      | ~ v5_pre_topc(k2_zfmisc_1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(B_743),u1_pre_topc(B_743)))),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0(B_743),u1_pre_topc(B_743)))
      | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0(B_743),u1_pre_topc(B_743)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_743))))
      | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0(B_743),u1_pre_topc(B_743)))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_743))
      | ~ l1_pre_topc(B_743)
      | ~ v2_pre_topc(B_743)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ v1_partfun1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0(B_743),u1_pre_topc(B_743)))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
      | ~ v1_funct_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0(B_743),u1_pre_topc(B_743))))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6622,c_8155])).

tff(c_8184,plain,(
    ! [B_744] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_744)
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0(B_744),u1_pre_topc(B_744)))
      | ~ l1_pre_topc(B_744)
      | ~ v2_pre_topc(B_744) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_4857,c_6622,c_4840,c_4857,c_6622,c_6622,c_7916,c_7540,c_4827,c_4857,c_6622,c_6622,c_4856,c_4857,c_6622,c_6622,c_4857,c_4857,c_6622,c_8157])).

tff(c_8204,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6659,c_8184])).

tff(c_8218,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_6665,c_8204])).

tff(c_6638,plain,(
    ! [D_621,A_622,B_623] :
      ( v5_pre_topc(D_621,A_622,B_623)
      | ~ v5_pre_topc(D_621,g1_pre_topc(u1_struct_0(A_622),u1_pre_topc(A_622)),B_623)
      | ~ m1_subset_1(D_621,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_622),u1_pre_topc(A_622))),u1_struct_0(B_623))))
      | ~ v1_funct_2(D_621,u1_struct_0(g1_pre_topc(u1_struct_0(A_622),u1_pre_topc(A_622))),u1_struct_0(B_623))
      | ~ m1_subset_1(D_621,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_622),u1_struct_0(B_623))))
      | ~ v1_funct_2(D_621,u1_struct_0(A_622),u1_struct_0(B_623))
      | ~ v1_funct_1(D_621)
      | ~ l1_pre_topc(B_623)
      | ~ v2_pre_topc(B_623)
      | ~ l1_pre_topc(A_622)
      | ~ v2_pre_topc(A_622) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_7051,plain,(
    ! [A_661,A_662,B_663] :
      ( v5_pre_topc(A_661,A_662,B_663)
      | ~ v5_pre_topc(A_661,g1_pre_topc(u1_struct_0(A_662),u1_pre_topc(A_662)),B_663)
      | ~ v1_funct_2(A_661,u1_struct_0(g1_pre_topc(u1_struct_0(A_662),u1_pre_topc(A_662))),u1_struct_0(B_663))
      | ~ m1_subset_1(A_661,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_662),u1_struct_0(B_663))))
      | ~ v1_funct_2(A_661,u1_struct_0(A_662),u1_struct_0(B_663))
      | ~ v1_funct_1(A_661)
      | ~ l1_pre_topc(B_663)
      | ~ v2_pre_topc(B_663)
      | ~ l1_pre_topc(A_662)
      | ~ v2_pre_topc(A_662)
      | ~ r1_tarski(A_661,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_662),u1_pre_topc(A_662))),u1_struct_0(B_663))) ) ),
    inference(resolution,[status(thm)],[c_18,c_6638])).

tff(c_7570,plain,(
    ! [A_710,B_711] :
      ( v5_pre_topc(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_710),u1_pre_topc(A_710))),u1_struct_0(B_711)),A_710,B_711)
      | ~ v5_pre_topc(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_710),u1_pre_topc(A_710))),u1_struct_0(B_711)),g1_pre_topc(u1_struct_0(A_710),u1_pre_topc(A_710)),B_711)
      | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_710),u1_pre_topc(A_710))),u1_struct_0(B_711)),u1_struct_0(g1_pre_topc(u1_struct_0(A_710),u1_pre_topc(A_710))),u1_struct_0(B_711))
      | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_710),u1_pre_topc(A_710))),u1_struct_0(B_711)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_710),u1_struct_0(B_711))))
      | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_710),u1_pre_topc(A_710))),u1_struct_0(B_711)),u1_struct_0(A_710),u1_struct_0(B_711))
      | ~ v1_funct_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_710),u1_pre_topc(A_710))),u1_struct_0(B_711)))
      | ~ l1_pre_topc(B_711)
      | ~ v2_pre_topc(B_711)
      | ~ l1_pre_topc(A_710)
      | ~ v2_pre_topc(A_710) ) ),
    inference(resolution,[status(thm)],[c_6,c_7051])).

tff(c_7588,plain,(
    ! [B_711] :
      ( v5_pre_topc(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_711)),'#skF_1',B_711)
      | ~ v5_pre_topc(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_711)),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_711)
      | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_711)),'#skF_4',u1_struct_0(B_711))
      | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_711)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_711))))
      | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_711)),u1_struct_0('#skF_1'),u1_struct_0(B_711))
      | ~ v1_funct_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_711)))
      | ~ l1_pre_topc(B_711)
      | ~ v2_pre_topc(B_711)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6622,c_7570])).

tff(c_7614,plain,(
    ! [B_711] :
      ( v5_pre_topc('#skF_4','#skF_1',B_711)
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_711)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0(B_711))
      | ~ l1_pre_topc(B_711)
      | ~ v2_pre_topc(B_711) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_80,c_4857,c_6622,c_4857,c_6622,c_4856,c_4857,c_6622,c_4827,c_4857,c_6622,c_4857,c_6622,c_4857,c_6622,c_7588])).

tff(c_8221,plain,
    ( v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_8218,c_7614])).

tff(c_8224,plain,(
    v5_pre_topc('#skF_4','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_6666,c_6659,c_8221])).

tff(c_8226,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_551,c_8224])).

tff(c_8227,plain,(
    u1_struct_0('#skF_1') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_6658])).

tff(c_8234,plain,(
    ~ v1_partfun1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8227,c_689])).

tff(c_8241,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4840,c_8234])).

tff(c_8242,plain,(
    u1_struct_0('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_672])).

tff(c_8251,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8242,c_193])).

tff(c_8254,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8242,c_103])).

tff(c_8255,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8242,c_78])).

tff(c_8253,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8242,c_76])).

tff(c_34,plain,(
    ! [A_20,B_21,C_22] :
      ( k1_relset_1(A_20,B_21,C_22) = k1_relat_1(C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_8469,plain,(
    k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8253,c_34])).

tff(c_8250,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8242,c_176])).

tff(c_13141,plain,(
    ! [B_1071,A_1072,C_1073] :
      ( k1_xboole_0 = B_1071
      | k1_relset_1(A_1072,B_1071,C_1073) = A_1072
      | ~ v1_funct_2(C_1073,A_1072,B_1071)
      | ~ m1_subset_1(C_1073,k1_zfmisc_1(k2_zfmisc_1(A_1072,B_1071))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_13337,plain,(
    ! [B_1096,A_1097,A_1098] :
      ( k1_xboole_0 = B_1096
      | k1_relset_1(A_1097,B_1096,A_1098) = A_1097
      | ~ v1_funct_2(A_1098,A_1097,B_1096)
      | ~ r1_tarski(A_1098,k2_zfmisc_1(A_1097,B_1096)) ) ),
    inference(resolution,[status(thm)],[c_18,c_13141])).

tff(c_13340,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0
    | k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') = u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(resolution,[status(thm)],[c_8250,c_13337])).

tff(c_13360,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8255,c_8469,c_13340])).

tff(c_13483,plain,(
    u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_13360])).

tff(c_8252,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8242,c_107])).

tff(c_8259,plain,
    ( v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_8242,c_62])).

tff(c_8275,plain,(
    v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_8259])).

tff(c_8268,plain,
    ( l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_8242,c_473])).

tff(c_8281,plain,(
    l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_8268])).

tff(c_8247,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8242,c_489])).

tff(c_13251,plain,(
    ! [D_1082,A_1083,B_1084] :
      ( v5_pre_topc(D_1082,A_1083,B_1084)
      | ~ v5_pre_topc(D_1082,A_1083,g1_pre_topc(u1_struct_0(B_1084),u1_pre_topc(B_1084)))
      | ~ m1_subset_1(D_1082,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1083),u1_struct_0(g1_pre_topc(u1_struct_0(B_1084),u1_pre_topc(B_1084))))))
      | ~ v1_funct_2(D_1082,u1_struct_0(A_1083),u1_struct_0(g1_pre_topc(u1_struct_0(B_1084),u1_pre_topc(B_1084))))
      | ~ m1_subset_1(D_1082,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1083),u1_struct_0(B_1084))))
      | ~ v1_funct_2(D_1082,u1_struct_0(A_1083),u1_struct_0(B_1084))
      | ~ v1_funct_1(D_1082)
      | ~ l1_pre_topc(B_1084)
      | ~ v2_pre_topc(B_1084)
      | ~ l1_pre_topc(A_1083)
      | ~ v2_pre_topc(A_1083) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_13254,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))
    | ~ v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_8253,c_13251])).

tff(c_13271,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8275,c_8281,c_90,c_88,c_80,c_8255,c_8247,c_13254])).

tff(c_13935,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8254,c_13483,c_8252,c_13483,c_13271])).

tff(c_13454,plain,(
    ! [D_1103,A_1104,B_1105] :
      ( v5_pre_topc(D_1103,A_1104,B_1105)
      | ~ v5_pre_topc(D_1103,g1_pre_topc(u1_struct_0(A_1104),u1_pre_topc(A_1104)),B_1105)
      | ~ m1_subset_1(D_1103,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1104),u1_pre_topc(A_1104))),u1_struct_0(B_1105))))
      | ~ v1_funct_2(D_1103,u1_struct_0(g1_pre_topc(u1_struct_0(A_1104),u1_pre_topc(A_1104))),u1_struct_0(B_1105))
      | ~ m1_subset_1(D_1103,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1104),u1_struct_0(B_1105))))
      | ~ v1_funct_2(D_1103,u1_struct_0(A_1104),u1_struct_0(B_1105))
      | ~ v1_funct_1(D_1103)
      | ~ l1_pre_topc(B_1105)
      | ~ v2_pre_topc(B_1105)
      | ~ l1_pre_topc(A_1104)
      | ~ v2_pre_topc(A_1104) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_14303,plain,(
    ! [A_1161,A_1162,B_1163] :
      ( v5_pre_topc(A_1161,A_1162,B_1163)
      | ~ v5_pre_topc(A_1161,g1_pre_topc(u1_struct_0(A_1162),u1_pre_topc(A_1162)),B_1163)
      | ~ v1_funct_2(A_1161,u1_struct_0(g1_pre_topc(u1_struct_0(A_1162),u1_pre_topc(A_1162))),u1_struct_0(B_1163))
      | ~ m1_subset_1(A_1161,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1162),u1_struct_0(B_1163))))
      | ~ v1_funct_2(A_1161,u1_struct_0(A_1162),u1_struct_0(B_1163))
      | ~ v1_funct_1(A_1161)
      | ~ l1_pre_topc(B_1163)
      | ~ v2_pre_topc(B_1163)
      | ~ l1_pre_topc(A_1162)
      | ~ v2_pre_topc(A_1162)
      | ~ r1_tarski(A_1161,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1162),u1_pre_topc(A_1162))),u1_struct_0(B_1163))) ) ),
    inference(resolution,[status(thm)],[c_18,c_13454])).

tff(c_14312,plain,(
    ! [A_1161,B_1163] :
      ( v5_pre_topc(A_1161,'#skF_1',B_1163)
      | ~ v5_pre_topc(A_1161,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_1163)
      | ~ v1_funct_2(A_1161,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_1163))
      | ~ m1_subset_1(A_1161,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_1163))))
      | ~ v1_funct_2(A_1161,u1_struct_0('#skF_1'),u1_struct_0(B_1163))
      | ~ v1_funct_1(A_1161)
      | ~ l1_pre_topc(B_1163)
      | ~ v2_pre_topc(B_1163)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r1_tarski(A_1161,k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(B_1163))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8242,c_14303])).

tff(c_14662,plain,(
    ! [A_1185,B_1186] :
      ( v5_pre_topc(A_1185,'#skF_1',B_1186)
      | ~ v5_pre_topc(A_1185,g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),B_1186)
      | ~ m1_subset_1(A_1185,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_1186))))
      | ~ v1_funct_2(A_1185,k1_relat_1('#skF_4'),u1_struct_0(B_1186))
      | ~ v1_funct_1(A_1185)
      | ~ l1_pre_topc(B_1186)
      | ~ v2_pre_topc(B_1186)
      | ~ r1_tarski(A_1185,k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_1186))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13483,c_94,c_92,c_8242,c_8242,c_13483,c_8242,c_8242,c_14312])).

tff(c_14671,plain,
    ( v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | ~ r1_tarski('#skF_4',k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_8252,c_14662])).

tff(c_14690,plain,(
    v5_pre_topc('#skF_4','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8251,c_90,c_88,c_80,c_8254,c_13935,c_14671])).

tff(c_14692,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_551,c_14690])).

tff(c_14693,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_13360])).

tff(c_14697,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14693,c_8250])).

tff(c_14702,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_14697])).

tff(c_163,plain,(
    ! [B_86,A_87] :
      ( B_86 = A_87
      | ~ r1_tarski(B_86,A_87)
      | ~ r1_tarski(A_87,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_168,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_161,c_163])).

tff(c_14782,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_14702,c_168])).

tff(c_14833,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_4',B_4) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14782,c_14782,c_12])).

tff(c_14835,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14782,c_14782,c_24])).

tff(c_13249,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2')) = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8242,c_8242,c_196])).

tff(c_13250,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_13249])).

tff(c_14868,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_4',u1_struct_0('#skF_2')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14835,c_13250])).

tff(c_15534,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_14833,c_14868])).

tff(c_15535,plain,(
    k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_13249])).

tff(c_15587,plain,
    ( u1_struct_0('#skF_2') = k1_xboole_0
    | k1_relat_1('#skF_4') = k1_xboole_0
    | k1_xboole_0 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_15535,c_8])).

tff(c_15695,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_15587])).

tff(c_8243,plain,(
    v1_partfun1('#skF_4',u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_672])).

tff(c_8285,plain,(
    v1_partfun1('#skF_4',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8242,c_8243])).

tff(c_13144,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0
    | k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') = u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(resolution,[status(thm)],[c_8253,c_13141])).

tff(c_13164,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0
    | k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') = u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8255,c_13144])).

tff(c_18557,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8469,c_13164])).

tff(c_18558,plain,(
    u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_18557])).

tff(c_18194,plain,
    ( u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8242,c_8242,c_669])).

tff(c_18195,plain,(
    ~ v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))) ),
    inference(splitLeft,[status(thm)],[c_18194])).

tff(c_18562,plain,(
    ~ v1_partfun1('#skF_4',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18558,c_18195])).

tff(c_18568,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8285,c_18562])).

tff(c_18569,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_18557])).

tff(c_15538,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15535,c_8252])).

tff(c_15948,plain,(
    ! [B_1265,A_1266,A_1267] :
      ( k1_xboole_0 = B_1265
      | k1_relset_1(A_1266,B_1265,A_1267) = A_1266
      | ~ v1_funct_2(A_1267,A_1266,B_1265)
      | ~ r1_tarski(A_1267,k2_zfmisc_1(A_1266,B_1265)) ) ),
    inference(resolution,[status(thm)],[c_18,c_13141])).

tff(c_15954,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0
    | k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') = u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(resolution,[status(thm)],[c_8250,c_15948])).

tff(c_15971,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8255,c_8469,c_15954])).

tff(c_16082,plain,(
    u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_15971])).

tff(c_15977,plain,
    ( u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8242,c_8242,c_669])).

tff(c_15978,plain,(
    ~ v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))) ),
    inference(splitLeft,[status(thm)],[c_15977])).

tff(c_16112,plain,(
    ~ v1_partfun1('#skF_4',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16082,c_15978])).

tff(c_16122,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8285,c_16112])).

tff(c_16123,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_15971])).

tff(c_15820,plain,
    ( k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8242,c_8242,c_246])).

tff(c_15821,plain,(
    ~ r1_tarski(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_15820])).

tff(c_16125,plain,(
    ~ r1_tarski(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),k1_xboole_0),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16123,c_15821])).

tff(c_16134,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_10,c_16125])).

tff(c_16135,plain,(
    u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_15977])).

tff(c_15911,plain,(
    ! [D_1261,A_1262,B_1263] :
      ( v5_pre_topc(D_1261,A_1262,B_1263)
      | ~ v5_pre_topc(D_1261,A_1262,g1_pre_topc(u1_struct_0(B_1263),u1_pre_topc(B_1263)))
      | ~ m1_subset_1(D_1261,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1262),u1_struct_0(g1_pre_topc(u1_struct_0(B_1263),u1_pre_topc(B_1263))))))
      | ~ v1_funct_2(D_1261,u1_struct_0(A_1262),u1_struct_0(g1_pre_topc(u1_struct_0(B_1263),u1_pre_topc(B_1263))))
      | ~ m1_subset_1(D_1261,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1262),u1_struct_0(B_1263))))
      | ~ v1_funct_2(D_1261,u1_struct_0(A_1262),u1_struct_0(B_1263))
      | ~ v1_funct_1(D_1261)
      | ~ l1_pre_topc(B_1263)
      | ~ v2_pre_topc(B_1263)
      | ~ l1_pre_topc(A_1262)
      | ~ v2_pre_topc(A_1262) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_15914,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))
    | ~ v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_8253,c_15911])).

tff(c_15931,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8275,c_8281,c_90,c_88,c_80,c_8255,c_8247,c_15914])).

tff(c_17044,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8254,c_16135,c_15538,c_15535,c_16135,c_15931])).

tff(c_15794,plain,(
    ! [D_1246,A_1247,B_1248] :
      ( v5_pre_topc(D_1246,A_1247,B_1248)
      | ~ v5_pre_topc(D_1246,g1_pre_topc(u1_struct_0(A_1247),u1_pre_topc(A_1247)),B_1248)
      | ~ m1_subset_1(D_1246,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1247),u1_pre_topc(A_1247))),u1_struct_0(B_1248))))
      | ~ v1_funct_2(D_1246,u1_struct_0(g1_pre_topc(u1_struct_0(A_1247),u1_pre_topc(A_1247))),u1_struct_0(B_1248))
      | ~ m1_subset_1(D_1246,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1247),u1_struct_0(B_1248))))
      | ~ v1_funct_2(D_1246,u1_struct_0(A_1247),u1_struct_0(B_1248))
      | ~ v1_funct_1(D_1246)
      | ~ l1_pre_topc(B_1248)
      | ~ v2_pre_topc(B_1248)
      | ~ l1_pre_topc(A_1247)
      | ~ v2_pre_topc(A_1247) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_17396,plain,(
    ! [A_1329,A_1330,B_1331] :
      ( v5_pre_topc(A_1329,A_1330,B_1331)
      | ~ v5_pre_topc(A_1329,g1_pre_topc(u1_struct_0(A_1330),u1_pre_topc(A_1330)),B_1331)
      | ~ v1_funct_2(A_1329,u1_struct_0(g1_pre_topc(u1_struct_0(A_1330),u1_pre_topc(A_1330))),u1_struct_0(B_1331))
      | ~ m1_subset_1(A_1329,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1330),u1_struct_0(B_1331))))
      | ~ v1_funct_2(A_1329,u1_struct_0(A_1330),u1_struct_0(B_1331))
      | ~ v1_funct_1(A_1329)
      | ~ l1_pre_topc(B_1331)
      | ~ v2_pre_topc(B_1331)
      | ~ l1_pre_topc(A_1330)
      | ~ v2_pre_topc(A_1330)
      | ~ r1_tarski(A_1329,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1330),u1_pre_topc(A_1330))),u1_struct_0(B_1331))) ) ),
    inference(resolution,[status(thm)],[c_18,c_15794])).

tff(c_17405,plain,(
    ! [A_1329,B_1331] :
      ( v5_pre_topc(A_1329,'#skF_1',B_1331)
      | ~ v5_pre_topc(A_1329,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_1331)
      | ~ v1_funct_2(A_1329,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_1331))
      | ~ m1_subset_1(A_1329,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_1331))))
      | ~ v1_funct_2(A_1329,u1_struct_0('#skF_1'),u1_struct_0(B_1331))
      | ~ v1_funct_1(A_1329)
      | ~ l1_pre_topc(B_1331)
      | ~ v2_pre_topc(B_1331)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r1_tarski(A_1329,k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(B_1331))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8242,c_17396])).

tff(c_18046,plain,(
    ! [A_1375,B_1376] :
      ( v5_pre_topc(A_1375,'#skF_1',B_1376)
      | ~ v5_pre_topc(A_1375,g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),B_1376)
      | ~ m1_subset_1(A_1375,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_1376))))
      | ~ v1_funct_2(A_1375,k1_relat_1('#skF_4'),u1_struct_0(B_1376))
      | ~ v1_funct_1(A_1375)
      | ~ l1_pre_topc(B_1376)
      | ~ v2_pre_topc(B_1376)
      | ~ r1_tarski(A_1375,k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_1376))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16135,c_94,c_92,c_8242,c_8242,c_16135,c_8242,c_8242,c_17405])).

tff(c_18055,plain,(
    ! [A_1375] :
      ( v5_pre_topc(A_1375,'#skF_1','#skF_2')
      | ~ v5_pre_topc(A_1375,g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),'#skF_2')
      | ~ m1_subset_1(A_1375,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_2(A_1375,k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(A_1375)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ r1_tarski(A_1375,k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15535,c_18046])).

tff(c_18149,plain,(
    ! [A_1379] :
      ( v5_pre_topc(A_1379,'#skF_1','#skF_2')
      | ~ v5_pre_topc(A_1379,g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),'#skF_2')
      | ~ m1_subset_1(A_1379,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_2(A_1379,k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(A_1379)
      | ~ r1_tarski(A_1379,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15535,c_90,c_88,c_18055])).

tff(c_18163,plain,
    ( v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4'))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_17044,c_18149])).

tff(c_18173,plain,(
    v5_pre_topc('#skF_4','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_80,c_8254,c_15538,c_18163])).

tff(c_18175,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_551,c_18173])).

tff(c_18176,plain,(
    k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_15820])).

tff(c_18573,plain,(
    k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),k1_xboole_0) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18569,c_18176])).

tff(c_18783,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_18573,c_10])).

tff(c_18805,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15695,c_18783])).

tff(c_18806,plain,(
    u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_18194])).

tff(c_19101,plain,(
    k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18806,c_18176])).

tff(c_18814,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18806,c_8255])).

tff(c_21219,plain,(
    ! [A_1508,A_1509,B_1510] :
      ( v5_pre_topc(A_1508,A_1509,B_1510)
      | ~ v5_pre_topc(A_1508,g1_pre_topc(u1_struct_0(A_1509),u1_pre_topc(A_1509)),B_1510)
      | ~ v1_funct_2(A_1508,u1_struct_0(g1_pre_topc(u1_struct_0(A_1509),u1_pre_topc(A_1509))),u1_struct_0(B_1510))
      | ~ m1_subset_1(A_1508,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1509),u1_struct_0(B_1510))))
      | ~ v1_funct_2(A_1508,u1_struct_0(A_1509),u1_struct_0(B_1510))
      | ~ v1_funct_1(A_1508)
      | ~ l1_pre_topc(B_1510)
      | ~ v2_pre_topc(B_1510)
      | ~ l1_pre_topc(A_1509)
      | ~ v2_pre_topc(A_1509)
      | ~ r1_tarski(A_1508,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1509),u1_pre_topc(A_1509))),u1_struct_0(B_1510))) ) ),
    inference(resolution,[status(thm)],[c_18,c_15794])).

tff(c_21228,plain,(
    ! [A_1508,B_1510] :
      ( v5_pre_topc(A_1508,'#skF_1',B_1510)
      | ~ v5_pre_topc(A_1508,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_1510)
      | ~ v1_funct_2(A_1508,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_1510))
      | ~ m1_subset_1(A_1508,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_1510))))
      | ~ v1_funct_2(A_1508,u1_struct_0('#skF_1'),u1_struct_0(B_1510))
      | ~ v1_funct_1(A_1508)
      | ~ l1_pre_topc(B_1510)
      | ~ v2_pre_topc(B_1510)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r1_tarski(A_1508,k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(B_1510))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8242,c_21219])).

tff(c_21933,plain,(
    ! [A_1549,B_1550] :
      ( v5_pre_topc(A_1549,'#skF_1',B_1550)
      | ~ v5_pre_topc(A_1549,g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),B_1550)
      | ~ m1_subset_1(A_1549,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_1550))))
      | ~ v1_funct_2(A_1549,k1_relat_1('#skF_4'),u1_struct_0(B_1550))
      | ~ v1_funct_1(A_1549)
      | ~ l1_pre_topc(B_1550)
      | ~ v2_pre_topc(B_1550)
      | ~ r1_tarski(A_1549,k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_1550))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18806,c_94,c_92,c_8242,c_8242,c_18806,c_8242,c_8242,c_21228])).

tff(c_22033,plain,(
    ! [A_1554,B_1555] :
      ( v5_pre_topc(A_1554,'#skF_1',B_1555)
      | ~ v5_pre_topc(A_1554,g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),B_1555)
      | ~ v1_funct_2(A_1554,k1_relat_1('#skF_4'),u1_struct_0(B_1555))
      | ~ v1_funct_1(A_1554)
      | ~ l1_pre_topc(B_1555)
      | ~ v2_pre_topc(B_1555)
      | ~ r1_tarski(A_1554,k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_1555))) ) ),
    inference(resolution,[status(thm)],[c_18,c_21933])).

tff(c_22074,plain,
    ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ r1_tarski('#skF_4',k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))) ),
    inference(resolution,[status(thm)],[c_8247,c_22033])).

tff(c_22108,plain,
    ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_19101,c_80,c_18814,c_22074])).

tff(c_22109,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_22108])).

tff(c_22112,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_22109])).

tff(c_22116,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_22112])).

tff(c_22117,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_22108])).

tff(c_22119,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_22117])).

tff(c_22122,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_473,c_22119])).

tff(c_22126,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_22122])).

tff(c_22127,plain,(
    v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_22117])).

tff(c_8684,plain,(
    ! [C_786,A_787,B_788] :
      ( v1_funct_2(C_786,A_787,B_788)
      | ~ v1_partfun1(C_786,A_787)
      | ~ v1_funct_1(C_786)
      | ~ m1_subset_1(C_786,k1_zfmisc_1(k2_zfmisc_1(A_787,B_788))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_19072,plain,(
    ! [A_1422,A_1423,B_1424] :
      ( v1_funct_2(A_1422,A_1423,B_1424)
      | ~ v1_partfun1(A_1422,A_1423)
      | ~ v1_funct_1(A_1422)
      | ~ r1_tarski(A_1422,k2_zfmisc_1(A_1423,B_1424)) ) ),
    inference(resolution,[status(thm)],[c_18,c_8684])).

tff(c_19099,plain,(
    ! [A_1423,B_1424] :
      ( v1_funct_2(k2_zfmisc_1(A_1423,B_1424),A_1423,B_1424)
      | ~ v1_partfun1(k2_zfmisc_1(A_1423,B_1424),A_1423)
      | ~ v1_funct_1(k2_zfmisc_1(A_1423,B_1424)) ) ),
    inference(resolution,[status(thm)],[c_6,c_19072])).

tff(c_19036,plain,(
    ! [D_1417,A_1418,B_1419] :
      ( v5_pre_topc(D_1417,A_1418,B_1419)
      | ~ v5_pre_topc(D_1417,A_1418,g1_pre_topc(u1_struct_0(B_1419),u1_pre_topc(B_1419)))
      | ~ m1_subset_1(D_1417,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1418),u1_struct_0(g1_pre_topc(u1_struct_0(B_1419),u1_pre_topc(B_1419))))))
      | ~ v1_funct_2(D_1417,u1_struct_0(A_1418),u1_struct_0(g1_pre_topc(u1_struct_0(B_1419),u1_pre_topc(B_1419))))
      | ~ m1_subset_1(D_1417,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1418),u1_struct_0(B_1419))))
      | ~ v1_funct_2(D_1417,u1_struct_0(A_1418),u1_struct_0(B_1419))
      | ~ v1_funct_1(D_1417)
      | ~ l1_pre_topc(B_1419)
      | ~ v2_pre_topc(B_1419)
      | ~ l1_pre_topc(A_1418)
      | ~ v2_pre_topc(A_1418) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_20997,plain,(
    ! [A_1495,A_1496,B_1497] :
      ( v5_pre_topc(A_1495,A_1496,B_1497)
      | ~ v5_pre_topc(A_1495,A_1496,g1_pre_topc(u1_struct_0(B_1497),u1_pre_topc(B_1497)))
      | ~ v1_funct_2(A_1495,u1_struct_0(A_1496),u1_struct_0(g1_pre_topc(u1_struct_0(B_1497),u1_pre_topc(B_1497))))
      | ~ m1_subset_1(A_1495,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1496),u1_struct_0(B_1497))))
      | ~ v1_funct_2(A_1495,u1_struct_0(A_1496),u1_struct_0(B_1497))
      | ~ v1_funct_1(A_1495)
      | ~ l1_pre_topc(B_1497)
      | ~ v2_pre_topc(B_1497)
      | ~ l1_pre_topc(A_1496)
      | ~ v2_pre_topc(A_1496)
      | ~ r1_tarski(A_1495,k2_zfmisc_1(u1_struct_0(A_1496),u1_struct_0(g1_pre_topc(u1_struct_0(B_1497),u1_pre_topc(B_1497))))) ) ),
    inference(resolution,[status(thm)],[c_18,c_19036])).

tff(c_21006,plain,(
    ! [A_1495,B_1497] :
      ( v5_pre_topc(A_1495,'#skF_1',B_1497)
      | ~ v5_pre_topc(A_1495,'#skF_1',g1_pre_topc(u1_struct_0(B_1497),u1_pre_topc(B_1497)))
      | ~ v1_funct_2(A_1495,u1_struct_0('#skF_1'),u1_struct_0(g1_pre_topc(u1_struct_0(B_1497),u1_pre_topc(B_1497))))
      | ~ m1_subset_1(A_1495,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_1497))))
      | ~ v1_funct_2(A_1495,u1_struct_0('#skF_1'),u1_struct_0(B_1497))
      | ~ v1_funct_1(A_1495)
      | ~ l1_pre_topc(B_1497)
      | ~ v2_pre_topc(B_1497)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r1_tarski(A_1495,k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0(B_1497),u1_pre_topc(B_1497))))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8242,c_20997])).

tff(c_23342,plain,(
    ! [A_1593,B_1594] :
      ( v5_pre_topc(A_1593,'#skF_1',B_1594)
      | ~ v5_pre_topc(A_1593,'#skF_1',g1_pre_topc(u1_struct_0(B_1594),u1_pre_topc(B_1594)))
      | ~ v1_funct_2(A_1593,k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0(B_1594),u1_pre_topc(B_1594))))
      | ~ m1_subset_1(A_1593,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_1594))))
      | ~ v1_funct_2(A_1593,k1_relat_1('#skF_4'),u1_struct_0(B_1594))
      | ~ v1_funct_1(A_1593)
      | ~ l1_pre_topc(B_1594)
      | ~ v2_pre_topc(B_1594)
      | ~ r1_tarski(A_1593,k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0(B_1594),u1_pre_topc(B_1594))))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_8242,c_8242,c_8242,c_21006])).

tff(c_23345,plain,(
    ! [A_1593] :
      ( v5_pre_topc(A_1593,'#skF_1','#skF_2')
      | ~ v5_pre_topc(A_1593,'#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v1_funct_2(A_1593,k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1(A_1593,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(A_1593,k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(A_1593)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ r1_tarski(A_1593,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19101,c_23342])).

tff(c_23370,plain,(
    ! [A_1595] :
      ( v5_pre_topc(A_1595,'#skF_1','#skF_2')
      | ~ v5_pre_topc(A_1595,'#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v1_funct_2(A_1595,k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1(A_1595,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_2(A_1595,k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(A_1595)
      | ~ r1_tarski(A_1595,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_15535,c_23345])).

tff(c_23386,plain,
    ( v5_pre_topc(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))),'#skF_1','#skF_2')
    | ~ v5_pre_topc(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))),'#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ m1_subset_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))),k1_zfmisc_1('#skF_4'))
    | ~ v1_funct_2(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))),k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))),'#skF_4')
    | ~ v1_partfun1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))),k1_relat_1('#skF_4'))
    | ~ v1_funct_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))) ),
    inference(resolution,[status(thm)],[c_19099,c_23370])).

tff(c_23408,plain,(
    v5_pre_topc('#skF_4','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_19101,c_8285,c_19101,c_6,c_19101,c_8254,c_19101,c_15538,c_19101,c_22127,c_19101,c_19101,c_23386])).

tff(c_23410,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_551,c_23408])).

tff(c_23412,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_15587])).

tff(c_23456,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23412,c_23412,c_24])).

tff(c_23532,plain,(
    v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23456,c_8275])).

tff(c_23529,plain,(
    l1_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23456,c_8281])).

tff(c_8404,plain,(
    ! [A_748,B_749,C_750] :
      ( k1_relset_1(A_748,B_749,C_750) = k1_relat_1(C_750)
      | ~ m1_subset_1(C_750,k1_zfmisc_1(k2_zfmisc_1(A_748,B_749))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_8415,plain,(
    ! [A_748,B_749] : k1_relset_1(A_748,B_749,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_8404])).

tff(c_8425,plain,(
    ! [A_748,B_749] : k1_relset_1(A_748,B_749,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_8415])).

tff(c_8524,plain,(
    ! [C_763,B_764] :
      ( v1_funct_2(C_763,k1_xboole_0,B_764)
      | k1_relset_1(k1_xboole_0,B_764,C_763) != k1_xboole_0
      | ~ m1_subset_1(C_763,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_44])).

tff(c_8530,plain,(
    ! [B_764] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_764)
      | k1_relset_1(k1_xboole_0,B_764,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14,c_8524])).

tff(c_8534,plain,(
    ! [B_764] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_764) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8425,c_8530])).

tff(c_23425,plain,(
    ! [B_764] : v1_funct_2('#skF_4','#skF_4',B_764) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23412,c_23412,c_8534])).

tff(c_23528,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23456,c_8255])).

tff(c_13155,plain,(
    ! [B_1071,A_1072] :
      ( k1_xboole_0 = B_1071
      | k1_relset_1(A_1072,B_1071,k1_xboole_0) = A_1072
      | ~ v1_funct_2(k1_xboole_0,A_1072,B_1071) ) ),
    inference(resolution,[status(thm)],[c_14,c_13141])).

tff(c_13170,plain,(
    ! [B_1071,A_1072] :
      ( k1_xboole_0 = B_1071
      | k1_xboole_0 = A_1072
      | ~ v1_funct_2(k1_xboole_0,A_1072,B_1071) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8425,c_13155])).

tff(c_24200,plain,(
    ! [B_1652,A_1653] :
      ( B_1652 = '#skF_4'
      | A_1653 = '#skF_4'
      | ~ v1_funct_2('#skF_4',A_1653,B_1652) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23412,c_23412,c_23412,c_13170])).

tff(c_24218,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = '#skF_4'
    | u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_23528,c_24200])).

tff(c_24229,plain,(
    u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))) = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_24218])).

tff(c_23453,plain,(
    ! [A_5] : m1_subset_1('#skF_4',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23412,c_14])).

tff(c_23518,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23456,c_8247])).

tff(c_23523,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23456,c_8253])).

tff(c_70,plain,(
    ! [D_64,A_50,B_58] :
      ( v5_pre_topc(D_64,A_50,B_58)
      | ~ v5_pre_topc(D_64,A_50,g1_pre_topc(u1_struct_0(B_58),u1_pre_topc(B_58)))
      | ~ m1_subset_1(D_64,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_50),u1_struct_0(g1_pre_topc(u1_struct_0(B_58),u1_pre_topc(B_58))))))
      | ~ v1_funct_2(D_64,u1_struct_0(A_50),u1_struct_0(g1_pre_topc(u1_struct_0(B_58),u1_pre_topc(B_58))))
      | ~ m1_subset_1(D_64,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_50),u1_struct_0(B_58))))
      | ~ v1_funct_2(D_64,u1_struct_0(A_50),u1_struct_0(B_58))
      | ~ v1_funct_1(D_64)
      | ~ l1_pre_topc(B_58)
      | ~ v2_pre_topc(B_58)
      | ~ l1_pre_topc(A_50)
      | ~ v2_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_23779,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),'#skF_2')
    | ~ v5_pre_topc('#skF_4',g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | ~ l1_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')))
    | ~ v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_23523,c_70])).

tff(c_23805,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),'#skF_2')
    | ~ v5_pre_topc('#skF_4',g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2'))
    | ~ l1_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')))
    | ~ v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_80,c_23528,c_23779])).

tff(c_24885,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23532,c_23529,c_23425,c_24229,c_23453,c_23518,c_23805])).

tff(c_23454,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_4',B_4) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23412,c_23412,c_12])).

tff(c_23536,plain,(
    u1_struct_0('#skF_1') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23456,c_8242])).

tff(c_23549,plain,(
    ! [D_1597,A_1598,B_1599] :
      ( v5_pre_topc(D_1597,A_1598,B_1599)
      | ~ v5_pre_topc(D_1597,g1_pre_topc(u1_struct_0(A_1598),u1_pre_topc(A_1598)),B_1599)
      | ~ m1_subset_1(D_1597,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1598),u1_pre_topc(A_1598))),u1_struct_0(B_1599))))
      | ~ v1_funct_2(D_1597,u1_struct_0(g1_pre_topc(u1_struct_0(A_1598),u1_pre_topc(A_1598))),u1_struct_0(B_1599))
      | ~ m1_subset_1(D_1597,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1598),u1_struct_0(B_1599))))
      | ~ v1_funct_2(D_1597,u1_struct_0(A_1598),u1_struct_0(B_1599))
      | ~ v1_funct_1(D_1597)
      | ~ l1_pre_topc(B_1599)
      | ~ v2_pre_topc(B_1599)
      | ~ l1_pre_topc(A_1598)
      | ~ v2_pre_topc(A_1598) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_24347,plain,(
    ! [A_1657,A_1658,B_1659] :
      ( v5_pre_topc(A_1657,A_1658,B_1659)
      | ~ v5_pre_topc(A_1657,g1_pre_topc(u1_struct_0(A_1658),u1_pre_topc(A_1658)),B_1659)
      | ~ v1_funct_2(A_1657,u1_struct_0(g1_pre_topc(u1_struct_0(A_1658),u1_pre_topc(A_1658))),u1_struct_0(B_1659))
      | ~ m1_subset_1(A_1657,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1658),u1_struct_0(B_1659))))
      | ~ v1_funct_2(A_1657,u1_struct_0(A_1658),u1_struct_0(B_1659))
      | ~ v1_funct_1(A_1657)
      | ~ l1_pre_topc(B_1659)
      | ~ v2_pre_topc(B_1659)
      | ~ l1_pre_topc(A_1658)
      | ~ v2_pre_topc(A_1658)
      | ~ r1_tarski(A_1657,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1658),u1_pre_topc(A_1658))),u1_struct_0(B_1659))) ) ),
    inference(resolution,[status(thm)],[c_18,c_23549])).

tff(c_24830,plain,(
    ! [A_1709,B_1710] :
      ( v5_pre_topc(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1709),u1_pre_topc(A_1709))),u1_struct_0(B_1710)),A_1709,B_1710)
      | ~ v5_pre_topc(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1709),u1_pre_topc(A_1709))),u1_struct_0(B_1710)),g1_pre_topc(u1_struct_0(A_1709),u1_pre_topc(A_1709)),B_1710)
      | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1709),u1_pre_topc(A_1709))),u1_struct_0(B_1710)),u1_struct_0(g1_pre_topc(u1_struct_0(A_1709),u1_pre_topc(A_1709))),u1_struct_0(B_1710))
      | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1709),u1_pre_topc(A_1709))),u1_struct_0(B_1710)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1709),u1_struct_0(B_1710))))
      | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1709),u1_pre_topc(A_1709))),u1_struct_0(B_1710)),u1_struct_0(A_1709),u1_struct_0(B_1710))
      | ~ v1_funct_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1709),u1_pre_topc(A_1709))),u1_struct_0(B_1710)))
      | ~ l1_pre_topc(B_1710)
      | ~ v2_pre_topc(B_1710)
      | ~ l1_pre_topc(A_1709)
      | ~ v2_pre_topc(A_1709) ) ),
    inference(resolution,[status(thm)],[c_6,c_24347])).

tff(c_24851,plain,(
    ! [B_1710] :
      ( v5_pre_topc(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_1710)),'#skF_1',B_1710)
      | ~ v5_pre_topc(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_1710)),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_1710)
      | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),u1_struct_0(B_1710)),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_1710))
      | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_1710)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_1710))))
      | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_1710)),u1_struct_0('#skF_1'),u1_struct_0(B_1710))
      | ~ v1_funct_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_1710)))
      | ~ l1_pre_topc(B_1710)
      | ~ v2_pre_topc(B_1710)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23536,c_24830])).

tff(c_24872,plain,(
    ! [B_1710] :
      ( v5_pre_topc('#skF_4','#skF_1',B_1710)
      | ~ v5_pre_topc('#skF_4',g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),B_1710)
      | ~ l1_pre_topc(B_1710)
      | ~ v2_pre_topc(B_1710) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_80,c_23454,c_24229,c_23536,c_23425,c_23454,c_24229,c_23536,c_23536,c_23453,c_23454,c_24229,c_23454,c_23536,c_23536,c_23425,c_24229,c_23454,c_24229,c_23536,c_23454,c_24229,c_23536,c_23536,c_23454,c_24229,c_23536,c_24851])).

tff(c_24888,plain,
    ( v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24885,c_24872])).

tff(c_24891,plain,(
    v5_pre_topc('#skF_4','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_24888])).

tff(c_24893,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_551,c_24891])).

tff(c_24894,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_24218])).

tff(c_60,plain,(
    ! [A_33] :
      ( m1_subset_1(u1_pre_topc(A_33),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_33))))
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_498,plain,(
    ! [A_138,B_139] :
      ( v1_pre_topc(g1_pre_topc(A_138,B_139))
      | ~ m1_subset_1(B_139,k1_zfmisc_1(k1_zfmisc_1(A_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_510,plain,(
    ! [A_33] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_33),u1_pre_topc(A_33)))
      | ~ l1_pre_topc(A_33) ) ),
    inference(resolution,[status(thm)],[c_60,c_498])).

tff(c_24975,plain,
    ( v1_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_24894,c_510])).

tff(c_25481,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_24975])).

tff(c_25484,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_473,c_25481])).

tff(c_25488,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_25484])).

tff(c_25490,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_24975])).

tff(c_24972,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_24894,c_62])).

tff(c_25803,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25490,c_24972])).

tff(c_25804,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_25803])).

tff(c_25808,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_25804])).

tff(c_25812,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_25808])).

tff(c_25814,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_25803])).

tff(c_23649,plain,(
    ! [D_1602,A_1603,B_1604] :
      ( v5_pre_topc(D_1602,A_1603,B_1604)
      | ~ v5_pre_topc(D_1602,A_1603,g1_pre_topc(u1_struct_0(B_1604),u1_pre_topc(B_1604)))
      | ~ m1_subset_1(D_1602,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1603),u1_struct_0(g1_pre_topc(u1_struct_0(B_1604),u1_pre_topc(B_1604))))))
      | ~ v1_funct_2(D_1602,u1_struct_0(A_1603),u1_struct_0(g1_pre_topc(u1_struct_0(B_1604),u1_pre_topc(B_1604))))
      | ~ m1_subset_1(D_1602,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1603),u1_struct_0(B_1604))))
      | ~ v1_funct_2(D_1602,u1_struct_0(A_1603),u1_struct_0(B_1604))
      | ~ v1_funct_1(D_1602)
      | ~ l1_pre_topc(B_1604)
      | ~ v2_pre_topc(B_1604)
      | ~ l1_pre_topc(A_1603)
      | ~ v2_pre_topc(A_1603) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_25020,plain,(
    ! [A_1713,A_1714,B_1715] :
      ( v5_pre_topc(A_1713,A_1714,B_1715)
      | ~ v5_pre_topc(A_1713,A_1714,g1_pre_topc(u1_struct_0(B_1715),u1_pre_topc(B_1715)))
      | ~ v1_funct_2(A_1713,u1_struct_0(A_1714),u1_struct_0(g1_pre_topc(u1_struct_0(B_1715),u1_pre_topc(B_1715))))
      | ~ m1_subset_1(A_1713,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1714),u1_struct_0(B_1715))))
      | ~ v1_funct_2(A_1713,u1_struct_0(A_1714),u1_struct_0(B_1715))
      | ~ v1_funct_1(A_1713)
      | ~ l1_pre_topc(B_1715)
      | ~ v2_pre_topc(B_1715)
      | ~ l1_pre_topc(A_1714)
      | ~ v2_pre_topc(A_1714)
      | ~ r1_tarski(A_1713,k2_zfmisc_1(u1_struct_0(A_1714),u1_struct_0(g1_pre_topc(u1_struct_0(B_1715),u1_pre_topc(B_1715))))) ) ),
    inference(resolution,[status(thm)],[c_18,c_23649])).

tff(c_25821,plain,(
    ! [A_1785,B_1786] :
      ( v5_pre_topc(k2_zfmisc_1(u1_struct_0(A_1785),u1_struct_0(g1_pre_topc(u1_struct_0(B_1786),u1_pre_topc(B_1786)))),A_1785,B_1786)
      | ~ v5_pre_topc(k2_zfmisc_1(u1_struct_0(A_1785),u1_struct_0(g1_pre_topc(u1_struct_0(B_1786),u1_pre_topc(B_1786)))),A_1785,g1_pre_topc(u1_struct_0(B_1786),u1_pre_topc(B_1786)))
      | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(A_1785),u1_struct_0(g1_pre_topc(u1_struct_0(B_1786),u1_pre_topc(B_1786)))),u1_struct_0(A_1785),u1_struct_0(g1_pre_topc(u1_struct_0(B_1786),u1_pre_topc(B_1786))))
      | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(A_1785),u1_struct_0(g1_pre_topc(u1_struct_0(B_1786),u1_pre_topc(B_1786)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1785),u1_struct_0(B_1786))))
      | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(A_1785),u1_struct_0(g1_pre_topc(u1_struct_0(B_1786),u1_pre_topc(B_1786)))),u1_struct_0(A_1785),u1_struct_0(B_1786))
      | ~ v1_funct_1(k2_zfmisc_1(u1_struct_0(A_1785),u1_struct_0(g1_pre_topc(u1_struct_0(B_1786),u1_pre_topc(B_1786)))))
      | ~ l1_pre_topc(B_1786)
      | ~ v2_pre_topc(B_1786)
      | ~ l1_pre_topc(A_1785)
      | ~ v2_pre_topc(A_1785) ) ),
    inference(resolution,[status(thm)],[c_6,c_25020])).

tff(c_25848,plain,(
    ! [B_1786] :
      ( v5_pre_topc(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(g1_pre_topc(u1_struct_0(B_1786),u1_pre_topc(B_1786)))),'#skF_1',B_1786)
      | ~ v5_pre_topc(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(g1_pre_topc(u1_struct_0(B_1786),u1_pre_topc(B_1786)))),'#skF_1',g1_pre_topc(u1_struct_0(B_1786),u1_pre_topc(B_1786)))
      | ~ v1_funct_2(k2_zfmisc_1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(B_1786),u1_pre_topc(B_1786)))),u1_struct_0('#skF_1'),u1_struct_0(g1_pre_topc(u1_struct_0(B_1786),u1_pre_topc(B_1786))))
      | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(g1_pre_topc(u1_struct_0(B_1786),u1_pre_topc(B_1786)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_1786))))
      | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(g1_pre_topc(u1_struct_0(B_1786),u1_pre_topc(B_1786)))),u1_struct_0('#skF_1'),u1_struct_0(B_1786))
      | ~ v1_funct_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(g1_pre_topc(u1_struct_0(B_1786),u1_pre_topc(B_1786)))))
      | ~ l1_pre_topc(B_1786)
      | ~ v2_pre_topc(B_1786)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23536,c_25821])).

tff(c_25880,plain,(
    ! [B_1787] :
      ( v5_pre_topc('#skF_4','#skF_1',B_1787)
      | ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0(B_1787),u1_pre_topc(B_1787)))
      | ~ l1_pre_topc(B_1787)
      | ~ v2_pre_topc(B_1787) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_80,c_23454,c_23536,c_23425,c_23536,c_23454,c_23536,c_23453,c_23454,c_23536,c_23425,c_23536,c_23454,c_23454,c_23536,c_23454,c_23536,c_25848])).

tff(c_25886,plain,
    ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_24894,c_25880])).

tff(c_25892,plain,
    ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25814,c_25490,c_25886])).

tff(c_25896,plain,(
    ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))) ),
    inference(splitLeft,[status(thm)],[c_25892])).

tff(c_23912,plain,(
    ! [D_1611,A_1612,B_1613] :
      ( v5_pre_topc(D_1611,A_1612,g1_pre_topc(u1_struct_0(B_1613),u1_pre_topc(B_1613)))
      | ~ v5_pre_topc(D_1611,A_1612,B_1613)
      | ~ m1_subset_1(D_1611,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1612),u1_struct_0(g1_pre_topc(u1_struct_0(B_1613),u1_pre_topc(B_1613))))))
      | ~ v1_funct_2(D_1611,u1_struct_0(A_1612),u1_struct_0(g1_pre_topc(u1_struct_0(B_1613),u1_pre_topc(B_1613))))
      | ~ m1_subset_1(D_1611,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1612),u1_struct_0(B_1613))))
      | ~ v1_funct_2(D_1611,u1_struct_0(A_1612),u1_struct_0(B_1613))
      | ~ v1_funct_1(D_1611)
      | ~ l1_pre_topc(B_1613)
      | ~ v2_pre_topc(B_1613)
      | ~ l1_pre_topc(A_1612)
      | ~ v2_pre_topc(A_1612) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_24166,plain,(
    ! [A_1647,A_1648,B_1649] :
      ( v5_pre_topc(A_1647,A_1648,g1_pre_topc(u1_struct_0(B_1649),u1_pre_topc(B_1649)))
      | ~ v5_pre_topc(A_1647,A_1648,B_1649)
      | ~ v1_funct_2(A_1647,u1_struct_0(A_1648),u1_struct_0(g1_pre_topc(u1_struct_0(B_1649),u1_pre_topc(B_1649))))
      | ~ m1_subset_1(A_1647,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1648),u1_struct_0(B_1649))))
      | ~ v1_funct_2(A_1647,u1_struct_0(A_1648),u1_struct_0(B_1649))
      | ~ v1_funct_1(A_1647)
      | ~ l1_pre_topc(B_1649)
      | ~ v2_pre_topc(B_1649)
      | ~ l1_pre_topc(A_1648)
      | ~ v2_pre_topc(A_1648)
      | ~ r1_tarski(A_1647,k2_zfmisc_1(u1_struct_0(A_1648),u1_struct_0(g1_pre_topc(u1_struct_0(B_1649),u1_pre_topc(B_1649))))) ) ),
    inference(resolution,[status(thm)],[c_18,c_23912])).

tff(c_25515,plain,(
    ! [A_1764,B_1765] :
      ( v5_pre_topc(k2_zfmisc_1(u1_struct_0(A_1764),u1_struct_0(g1_pre_topc(u1_struct_0(B_1765),u1_pre_topc(B_1765)))),A_1764,g1_pre_topc(u1_struct_0(B_1765),u1_pre_topc(B_1765)))
      | ~ v5_pre_topc(k2_zfmisc_1(u1_struct_0(A_1764),u1_struct_0(g1_pre_topc(u1_struct_0(B_1765),u1_pre_topc(B_1765)))),A_1764,B_1765)
      | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(A_1764),u1_struct_0(g1_pre_topc(u1_struct_0(B_1765),u1_pre_topc(B_1765)))),u1_struct_0(A_1764),u1_struct_0(g1_pre_topc(u1_struct_0(B_1765),u1_pre_topc(B_1765))))
      | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(A_1764),u1_struct_0(g1_pre_topc(u1_struct_0(B_1765),u1_pre_topc(B_1765)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1764),u1_struct_0(B_1765))))
      | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(A_1764),u1_struct_0(g1_pre_topc(u1_struct_0(B_1765),u1_pre_topc(B_1765)))),u1_struct_0(A_1764),u1_struct_0(B_1765))
      | ~ v1_funct_1(k2_zfmisc_1(u1_struct_0(A_1764),u1_struct_0(g1_pre_topc(u1_struct_0(B_1765),u1_pre_topc(B_1765)))))
      | ~ l1_pre_topc(B_1765)
      | ~ v2_pre_topc(B_1765)
      | ~ l1_pre_topc(A_1764)
      | ~ v2_pre_topc(A_1764) ) ),
    inference(resolution,[status(thm)],[c_6,c_24166])).

tff(c_25542,plain,(
    ! [B_1765] :
      ( v5_pre_topc(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(g1_pre_topc(u1_struct_0(B_1765),u1_pre_topc(B_1765)))),'#skF_1',g1_pre_topc(u1_struct_0(B_1765),u1_pre_topc(B_1765)))
      | ~ v5_pre_topc(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(g1_pre_topc(u1_struct_0(B_1765),u1_pre_topc(B_1765)))),'#skF_1',B_1765)
      | ~ v1_funct_2(k2_zfmisc_1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(B_1765),u1_pre_topc(B_1765)))),u1_struct_0('#skF_1'),u1_struct_0(g1_pre_topc(u1_struct_0(B_1765),u1_pre_topc(B_1765))))
      | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(g1_pre_topc(u1_struct_0(B_1765),u1_pre_topc(B_1765)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_1765))))
      | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(g1_pre_topc(u1_struct_0(B_1765),u1_pre_topc(B_1765)))),u1_struct_0('#skF_1'),u1_struct_0(B_1765))
      | ~ v1_funct_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(g1_pre_topc(u1_struct_0(B_1765),u1_pre_topc(B_1765)))))
      | ~ l1_pre_topc(B_1765)
      | ~ v2_pre_topc(B_1765)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23536,c_25515])).

tff(c_25574,plain,(
    ! [B_1766] :
      ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0(B_1766),u1_pre_topc(B_1766)))
      | ~ v5_pre_topc('#skF_4','#skF_1',B_1766)
      | ~ l1_pre_topc(B_1766)
      | ~ v2_pre_topc(B_1766) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_80,c_23454,c_23536,c_23425,c_23536,c_23454,c_23536,c_23453,c_23454,c_23536,c_23425,c_23536,c_23454,c_23454,c_23536,c_23454,c_23536,c_25542])).

tff(c_25577,plain,
    ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
    | ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_24894,c_25574])).

tff(c_25582,plain,
    ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
    | ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25490,c_25577])).

tff(c_26035,plain,
    ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
    | ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25814,c_25582])).

tff(c_26036,plain,(
    ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_25896,c_26035])).

tff(c_24896,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24894,c_23528])).

tff(c_23825,plain,(
    ! [A_1608] : m1_subset_1('#skF_4',k1_zfmisc_1(A_1608)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23412,c_14])).

tff(c_66,plain,(
    ! [D_49,A_35,B_43] :
      ( v5_pre_topc(D_49,A_35,B_43)
      | ~ v5_pre_topc(D_49,g1_pre_topc(u1_struct_0(A_35),u1_pre_topc(A_35)),B_43)
      | ~ m1_subset_1(D_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_35),u1_pre_topc(A_35))),u1_struct_0(B_43))))
      | ~ v1_funct_2(D_49,u1_struct_0(g1_pre_topc(u1_struct_0(A_35),u1_pre_topc(A_35))),u1_struct_0(B_43))
      | ~ m1_subset_1(D_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_35),u1_struct_0(B_43))))
      | ~ v1_funct_2(D_49,u1_struct_0(A_35),u1_struct_0(B_43))
      | ~ v1_funct_1(D_49)
      | ~ l1_pre_topc(B_43)
      | ~ v2_pre_topc(B_43)
      | ~ l1_pre_topc(A_35)
      | ~ v2_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_23833,plain,(
    ! [A_35,B_43] :
      ( v5_pre_topc('#skF_4',A_35,B_43)
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_35),u1_pre_topc(A_35)),B_43)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_35),u1_pre_topc(A_35))),u1_struct_0(B_43))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_35),u1_struct_0(B_43))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_35),u1_struct_0(B_43))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(B_43)
      | ~ v2_pre_topc(B_43)
      | ~ l1_pre_topc(A_35)
      | ~ v2_pre_topc(A_35) ) ),
    inference(resolution,[status(thm)],[c_23825,c_66])).

tff(c_27161,plain,(
    ! [A_1836,B_1837] :
      ( v5_pre_topc('#skF_4',A_1836,B_1837)
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_1836),u1_pre_topc(A_1836)),B_1837)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_1836),u1_pre_topc(A_1836))),u1_struct_0(B_1837))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1836),u1_struct_0(B_1837))
      | ~ l1_pre_topc(B_1837)
      | ~ v2_pre_topc(B_1837)
      | ~ l1_pre_topc(A_1836)
      | ~ v2_pre_topc(A_1836) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_23453,c_23833])).

tff(c_27179,plain,(
    ! [B_1837] :
      ( v5_pre_topc('#skF_4','#skF_1',B_1837)
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_1837)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),u1_struct_0(B_1837))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0(B_1837))
      | ~ l1_pre_topc(B_1837)
      | ~ v2_pre_topc(B_1837)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23536,c_27161])).

tff(c_27195,plain,(
    ! [B_1838] :
      ( v5_pre_topc('#skF_4','#skF_1',B_1838)
      | ~ v5_pre_topc('#skF_4',g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),B_1838)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),u1_struct_0(B_1838))
      | ~ l1_pre_topc(B_1838)
      | ~ v2_pre_topc(B_1838) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_23425,c_23536,c_23536,c_27179])).

tff(c_27198,plain,
    ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4',g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),'#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_24894,c_27195])).

tff(c_27209,plain,(
    v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25814,c_25490,c_24896,c_23518,c_27198])).

tff(c_27211,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26036,c_27209])).

tff(c_27212,plain,(
    v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_25892])).

tff(c_25873,plain,(
    ! [B_1786] :
      ( v5_pre_topc('#skF_4','#skF_1',B_1786)
      | ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0(B_1786),u1_pre_topc(B_1786)))
      | ~ l1_pre_topc(B_1786)
      | ~ v2_pre_topc(B_1786) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_80,c_23454,c_23536,c_23425,c_23536,c_23454,c_23536,c_23453,c_23454,c_23536,c_23425,c_23536,c_23454,c_23454,c_23536,c_23454,c_23536,c_25848])).

tff(c_27216,plain,
    ( v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_27212,c_25873])).

tff(c_27219,plain,(
    v5_pre_topc('#skF_4','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_27216])).

tff(c_27221,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_551,c_27219])).

tff(c_27222,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_27443,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_489,c_27222])).

tff(c_27444,plain,(
    v5_pre_topc('#skF_4','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_32270,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_4',B_4) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32208,c_32208,c_12])).

tff(c_32272,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32208,c_32208,c_24])).

tff(c_32632,plain,
    ( u1_struct_0('#skF_1') = '#skF_4'
    | u1_struct_0('#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32208,c_32208,c_32207])).

tff(c_32633,plain,(
    u1_struct_0('#skF_2') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_32632])).

tff(c_32638,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32633,c_103])).

tff(c_32271,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32208,c_32208,c_10])).

tff(c_32639,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32633,c_78])).

tff(c_30573,plain,(
    ! [A_2122,B_2123] : k1_relset_1(A_2122,B_2123,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_30559])).

tff(c_30584,plain,(
    ! [A_2122,B_2123] : k1_relset_1(A_2122,B_2123,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_30573])).

tff(c_31360,plain,(
    ! [B_2196,A_2197] :
      ( k1_xboole_0 = B_2196
      | k1_relset_1(A_2197,B_2196,k1_xboole_0) = A_2197
      | ~ v1_funct_2(k1_xboole_0,A_2197,B_2196) ) ),
    inference(resolution,[status(thm)],[c_14,c_31346])).

tff(c_31369,plain,(
    ! [B_2196,A_2197] :
      ( k1_xboole_0 = B_2196
      | k1_xboole_0 = A_2197
      | ~ v1_funct_2(k1_xboole_0,A_2197,B_2196) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30584,c_31360])).

tff(c_32836,plain,(
    ! [B_2301,A_2302] :
      ( B_2301 = '#skF_4'
      | A_2302 = '#skF_4'
      | ~ v1_funct_2('#skF_4',A_2302,B_2301) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32208,c_32208,c_32208,c_31369])).

tff(c_32859,plain,
    ( u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) = '#skF_4'
    | u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_32639,c_32836])).

tff(c_32876,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_32859])).

tff(c_27614,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_405,c_27605])).

tff(c_27627,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_27614])).

tff(c_32326,plain,(
    ~ v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(splitLeft,[status(thm)],[c_27627])).

tff(c_32878,plain,(
    ~ v1_partfun1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32876,c_32326])).

tff(c_32882,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32253,c_32878])).

tff(c_32883,plain,(
    u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_32859])).

tff(c_32269,plain,(
    ! [A_5] : m1_subset_1('#skF_4',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32208,c_14])).

tff(c_32710,plain,(
    ! [D_2279,A_2280,B_2281] :
      ( v5_pre_topc(D_2279,A_2280,g1_pre_topc(u1_struct_0(B_2281),u1_pre_topc(B_2281)))
      | ~ v5_pre_topc(D_2279,A_2280,B_2281)
      | ~ m1_subset_1(D_2279,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2280),u1_struct_0(g1_pre_topc(u1_struct_0(B_2281),u1_pre_topc(B_2281))))))
      | ~ v1_funct_2(D_2279,u1_struct_0(A_2280),u1_struct_0(g1_pre_topc(u1_struct_0(B_2281),u1_pre_topc(B_2281))))
      | ~ m1_subset_1(D_2279,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2280),u1_struct_0(B_2281))))
      | ~ v1_funct_2(D_2279,u1_struct_0(A_2280),u1_struct_0(B_2281))
      | ~ v1_funct_1(D_2279)
      | ~ l1_pre_topc(B_2281)
      | ~ v2_pre_topc(B_2281)
      | ~ l1_pre_topc(A_2280)
      | ~ v2_pre_topc(A_2280) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_33349,plain,(
    ! [A_2346,A_2347,B_2348] :
      ( v5_pre_topc(A_2346,A_2347,g1_pre_topc(u1_struct_0(B_2348),u1_pre_topc(B_2348)))
      | ~ v5_pre_topc(A_2346,A_2347,B_2348)
      | ~ v1_funct_2(A_2346,u1_struct_0(A_2347),u1_struct_0(g1_pre_topc(u1_struct_0(B_2348),u1_pre_topc(B_2348))))
      | ~ m1_subset_1(A_2346,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2347),u1_struct_0(B_2348))))
      | ~ v1_funct_2(A_2346,u1_struct_0(A_2347),u1_struct_0(B_2348))
      | ~ v1_funct_1(A_2346)
      | ~ l1_pre_topc(B_2348)
      | ~ v2_pre_topc(B_2348)
      | ~ l1_pre_topc(A_2347)
      | ~ v2_pre_topc(A_2347)
      | ~ r1_tarski(A_2346,k2_zfmisc_1(u1_struct_0(A_2347),u1_struct_0(g1_pre_topc(u1_struct_0(B_2348),u1_pre_topc(B_2348))))) ) ),
    inference(resolution,[status(thm)],[c_18,c_32710])).

tff(c_33754,plain,(
    ! [A_2383,B_2384] :
      ( v5_pre_topc(k2_zfmisc_1(u1_struct_0(A_2383),u1_struct_0(g1_pre_topc(u1_struct_0(B_2384),u1_pre_topc(B_2384)))),A_2383,g1_pre_topc(u1_struct_0(B_2384),u1_pre_topc(B_2384)))
      | ~ v5_pre_topc(k2_zfmisc_1(u1_struct_0(A_2383),u1_struct_0(g1_pre_topc(u1_struct_0(B_2384),u1_pre_topc(B_2384)))),A_2383,B_2384)
      | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(A_2383),u1_struct_0(g1_pre_topc(u1_struct_0(B_2384),u1_pre_topc(B_2384)))),u1_struct_0(A_2383),u1_struct_0(g1_pre_topc(u1_struct_0(B_2384),u1_pre_topc(B_2384))))
      | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(A_2383),u1_struct_0(g1_pre_topc(u1_struct_0(B_2384),u1_pre_topc(B_2384)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2383),u1_struct_0(B_2384))))
      | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(A_2383),u1_struct_0(g1_pre_topc(u1_struct_0(B_2384),u1_pre_topc(B_2384)))),u1_struct_0(A_2383),u1_struct_0(B_2384))
      | ~ v1_funct_1(k2_zfmisc_1(u1_struct_0(A_2383),u1_struct_0(g1_pre_topc(u1_struct_0(B_2384),u1_pre_topc(B_2384)))))
      | ~ l1_pre_topc(B_2384)
      | ~ v2_pre_topc(B_2384)
      | ~ l1_pre_topc(A_2383)
      | ~ v2_pre_topc(A_2383) ) ),
    inference(resolution,[status(thm)],[c_6,c_33349])).

tff(c_33784,plain,(
    ! [A_2383] :
      ( v5_pre_topc(k2_zfmisc_1(u1_struct_0(A_2383),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))),A_2383,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc(k2_zfmisc_1(u1_struct_0(A_2383),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))),A_2383,'#skF_2')
      | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(A_2383),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))),u1_struct_0(A_2383),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(A_2383),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2383),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(A_2383),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))),u1_struct_0(A_2383),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_zfmisc_1(u1_struct_0(A_2383),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_2383)
      | ~ v2_pre_topc(A_2383) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32633,c_33754])).

tff(c_33802,plain,(
    ! [A_2383] :
      ( v5_pre_topc('#skF_4',A_2383,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc('#skF_4',A_2383,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_2383),'#skF_4')
      | ~ l1_pre_topc(A_2383)
      | ~ v2_pre_topc(A_2383) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_80,c_32271,c_32883,c_32633,c_32271,c_32883,c_32633,c_32633,c_32269,c_32271,c_32883,c_32271,c_32633,c_32633,c_32883,c_32271,c_32883,c_32633,c_32271,c_32883,c_32633,c_32271,c_32883,c_32633,c_32633,c_33784])).

tff(c_32885,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32883,c_32639])).

tff(c_32668,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_32633,c_62])).

tff(c_32700,plain,(
    v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_32668])).

tff(c_32677,plain,
    ( l1_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_32633,c_473])).

tff(c_32706,plain,(
    l1_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_32677])).

tff(c_32563,plain,(
    ! [D_2269,A_2270,B_2271] :
      ( v5_pre_topc(D_2269,g1_pre_topc(u1_struct_0(A_2270),u1_pre_topc(A_2270)),B_2271)
      | ~ v5_pre_topc(D_2269,A_2270,B_2271)
      | ~ m1_subset_1(D_2269,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2270),u1_pre_topc(A_2270))),u1_struct_0(B_2271))))
      | ~ v1_funct_2(D_2269,u1_struct_0(g1_pre_topc(u1_struct_0(A_2270),u1_pre_topc(A_2270))),u1_struct_0(B_2271))
      | ~ m1_subset_1(D_2269,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2270),u1_struct_0(B_2271))))
      | ~ v1_funct_2(D_2269,u1_struct_0(A_2270),u1_struct_0(B_2271))
      | ~ v1_funct_1(D_2269)
      | ~ l1_pre_topc(B_2271)
      | ~ v2_pre_topc(B_2271)
      | ~ l1_pre_topc(A_2270)
      | ~ v2_pre_topc(A_2270) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_33256,plain,(
    ! [A_2338,A_2339,B_2340] :
      ( v5_pre_topc(A_2338,g1_pre_topc(u1_struct_0(A_2339),u1_pre_topc(A_2339)),B_2340)
      | ~ v5_pre_topc(A_2338,A_2339,B_2340)
      | ~ v1_funct_2(A_2338,u1_struct_0(g1_pre_topc(u1_struct_0(A_2339),u1_pre_topc(A_2339))),u1_struct_0(B_2340))
      | ~ m1_subset_1(A_2338,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2339),u1_struct_0(B_2340))))
      | ~ v1_funct_2(A_2338,u1_struct_0(A_2339),u1_struct_0(B_2340))
      | ~ v1_funct_1(A_2338)
      | ~ l1_pre_topc(B_2340)
      | ~ v2_pre_topc(B_2340)
      | ~ l1_pre_topc(A_2339)
      | ~ v2_pre_topc(A_2339)
      | ~ r1_tarski(A_2338,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2339),u1_pre_topc(A_2339))),u1_struct_0(B_2340))) ) ),
    inference(resolution,[status(thm)],[c_18,c_32563])).

tff(c_33853,plain,(
    ! [A_2387,B_2388] :
      ( v5_pre_topc(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2387),u1_pre_topc(A_2387))),u1_struct_0(B_2388)),g1_pre_topc(u1_struct_0(A_2387),u1_pre_topc(A_2387)),B_2388)
      | ~ v5_pre_topc(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2387),u1_pre_topc(A_2387))),u1_struct_0(B_2388)),A_2387,B_2388)
      | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2387),u1_pre_topc(A_2387))),u1_struct_0(B_2388)),u1_struct_0(g1_pre_topc(u1_struct_0(A_2387),u1_pre_topc(A_2387))),u1_struct_0(B_2388))
      | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2387),u1_pre_topc(A_2387))),u1_struct_0(B_2388)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2387),u1_struct_0(B_2388))))
      | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2387),u1_pre_topc(A_2387))),u1_struct_0(B_2388)),u1_struct_0(A_2387),u1_struct_0(B_2388))
      | ~ v1_funct_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2387),u1_pre_topc(A_2387))),u1_struct_0(B_2388)))
      | ~ l1_pre_topc(B_2388)
      | ~ v2_pre_topc(B_2388)
      | ~ l1_pre_topc(A_2387)
      | ~ v2_pre_topc(A_2387) ) ),
    inference(resolution,[status(thm)],[c_6,c_33256])).

tff(c_33865,plain,(
    ! [A_2387] :
      ( v5_pre_topc(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2387),u1_pre_topc(A_2387))),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))),g1_pre_topc(u1_struct_0(A_2387),u1_pre_topc(A_2387)),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2387),u1_pre_topc(A_2387))),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))),A_2387,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2387),u1_pre_topc(A_2387))),'#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0(A_2387),u1_pre_topc(A_2387))),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2387),u1_pre_topc(A_2387))),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2387),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))))
      | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2387),u1_pre_topc(A_2387))),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))),u1_struct_0(A_2387),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
      | ~ v1_funct_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2387),u1_pre_topc(A_2387))),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))))
      | ~ l1_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_2387)
      | ~ v2_pre_topc(A_2387) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32883,c_33853])).

tff(c_34051,plain,(
    ! [A_2393] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_2393),u1_pre_topc(A_2393)),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc('#skF_4',A_2393,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_2393),u1_pre_topc(A_2393))),'#skF_4')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_2393),'#skF_4')
      | ~ l1_pre_topc(A_2393)
      | ~ v2_pre_topc(A_2393) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32700,c_32706,c_80,c_32271,c_32883,c_32883,c_32271,c_32883,c_32269,c_32271,c_32883,c_32883,c_32271,c_32271,c_32883,c_32271,c_32883,c_33865])).

tff(c_27470,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27444,c_106])).

tff(c_32637,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32633,c_27470])).

tff(c_34064,plain,
    ( ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34051,c_32637])).

tff(c_34078,plain,(
    ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_32638,c_32885,c_34064])).

tff(c_34087,plain,
    ( ~ v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_33802,c_34078])).

tff(c_34091,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_32638,c_27444,c_34087])).

tff(c_34092,plain,(
    u1_struct_0('#skF_1') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_32632])).

tff(c_34099,plain,(
    ~ v1_partfun1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34092,c_27647])).

tff(c_34106,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32253,c_34099])).

tff(c_34107,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_27627])).

tff(c_34606,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32272,c_34107])).

tff(c_30592,plain,(
    ! [C_2127,B_2128] :
      ( v1_funct_2(C_2127,k1_xboole_0,B_2128)
      | k1_relset_1(k1_xboole_0,B_2128,C_2127) != k1_xboole_0
      | ~ m1_subset_1(C_2127,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_44])).

tff(c_30598,plain,(
    ! [B_2128] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_2128)
      | k1_relset_1(k1_xboole_0,B_2128,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14,c_30592])).

tff(c_30602,plain,(
    ! [B_2128] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_2128) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30584,c_30598])).

tff(c_32244,plain,(
    ! [B_2128] : v1_funct_2('#skF_4','#skF_4',B_2128) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32208,c_32208,c_30602])).

tff(c_34424,plain,(
    ! [D_2419,A_2420,B_2421] :
      ( v5_pre_topc(D_2419,g1_pre_topc(u1_struct_0(A_2420),u1_pre_topc(A_2420)),B_2421)
      | ~ v5_pre_topc(D_2419,A_2420,B_2421)
      | ~ m1_subset_1(D_2419,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2420),u1_pre_topc(A_2420))),u1_struct_0(B_2421))))
      | ~ v1_funct_2(D_2419,u1_struct_0(g1_pre_topc(u1_struct_0(A_2420),u1_pre_topc(A_2420))),u1_struct_0(B_2421))
      | ~ m1_subset_1(D_2419,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2420),u1_struct_0(B_2421))))
      | ~ v1_funct_2(D_2419,u1_struct_0(A_2420),u1_struct_0(B_2421))
      | ~ v1_funct_1(D_2419)
      | ~ l1_pre_topc(B_2421)
      | ~ v2_pre_topc(B_2421)
      | ~ l1_pre_topc(A_2420)
      | ~ v2_pre_topc(A_2420) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_35230,plain,(
    ! [A_2492,A_2493,B_2494] :
      ( v5_pre_topc(A_2492,g1_pre_topc(u1_struct_0(A_2493),u1_pre_topc(A_2493)),B_2494)
      | ~ v5_pre_topc(A_2492,A_2493,B_2494)
      | ~ v1_funct_2(A_2492,u1_struct_0(g1_pre_topc(u1_struct_0(A_2493),u1_pre_topc(A_2493))),u1_struct_0(B_2494))
      | ~ m1_subset_1(A_2492,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2493),u1_struct_0(B_2494))))
      | ~ v1_funct_2(A_2492,u1_struct_0(A_2493),u1_struct_0(B_2494))
      | ~ v1_funct_1(A_2492)
      | ~ l1_pre_topc(B_2494)
      | ~ v2_pre_topc(B_2494)
      | ~ l1_pre_topc(A_2493)
      | ~ v2_pre_topc(A_2493)
      | ~ r1_tarski(A_2492,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2493),u1_pre_topc(A_2493))),u1_struct_0(B_2494))) ) ),
    inference(resolution,[status(thm)],[c_18,c_34424])).

tff(c_35575,plain,(
    ! [A_2516,B_2517] :
      ( v5_pre_topc(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2516),u1_pre_topc(A_2516))),u1_struct_0(B_2517)),g1_pre_topc(u1_struct_0(A_2516),u1_pre_topc(A_2516)),B_2517)
      | ~ v5_pre_topc(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2516),u1_pre_topc(A_2516))),u1_struct_0(B_2517)),A_2516,B_2517)
      | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2516),u1_pre_topc(A_2516))),u1_struct_0(B_2517)),u1_struct_0(g1_pre_topc(u1_struct_0(A_2516),u1_pre_topc(A_2516))),u1_struct_0(B_2517))
      | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2516),u1_pre_topc(A_2516))),u1_struct_0(B_2517)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2516),u1_struct_0(B_2517))))
      | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2516),u1_pre_topc(A_2516))),u1_struct_0(B_2517)),u1_struct_0(A_2516),u1_struct_0(B_2517))
      | ~ v1_funct_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2516),u1_pre_topc(A_2516))),u1_struct_0(B_2517)))
      | ~ l1_pre_topc(B_2517)
      | ~ v2_pre_topc(B_2517)
      | ~ l1_pre_topc(A_2516)
      | ~ v2_pre_topc(A_2516) ) ),
    inference(resolution,[status(thm)],[c_6,c_35230])).

tff(c_35587,plain,(
    ! [B_2517] :
      ( v5_pre_topc(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_2517)),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_2517)
      | ~ v5_pre_topc(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_2517)),'#skF_1',B_2517)
      | ~ v1_funct_2(k2_zfmisc_1('#skF_4',u1_struct_0(B_2517)),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_2517))
      | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_2517)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_2517))))
      | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_2517)),u1_struct_0('#skF_1'),u1_struct_0(B_2517))
      | ~ v1_funct_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_2517)))
      | ~ l1_pre_topc(B_2517)
      | ~ v2_pre_topc(B_2517)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34606,c_35575])).

tff(c_35617,plain,(
    ! [B_2517] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_2517)
      | ~ v5_pre_topc('#skF_4','#skF_1',B_2517)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0(B_2517))
      | ~ l1_pre_topc(B_2517)
      | ~ v2_pre_topc(B_2517) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_80,c_32270,c_34606,c_32270,c_34606,c_32269,c_32270,c_34606,c_32244,c_32270,c_34606,c_32270,c_34606,c_32270,c_34606,c_35587])).

tff(c_34447,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34444,c_27470])).

tff(c_474,plain,(
    ! [A_132] :
      ( r1_tarski(u1_pre_topc(A_132),k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ l1_pre_topc(A_132) ) ),
    inference(resolution,[status(thm)],[c_466,c_16])).

tff(c_34662,plain,
    ( r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),k1_zfmisc_1('#skF_4'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_34606,c_474])).

tff(c_35266,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_34662])).

tff(c_35269,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_473,c_35266])).

tff(c_35273,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_35269])).

tff(c_35275,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_34662])).

tff(c_34656,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_34606,c_62])).

tff(c_35564,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35275,c_34656])).

tff(c_35565,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_35564])).

tff(c_35568,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_35565])).

tff(c_35572,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_35568])).

tff(c_35574,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_35564])).

tff(c_34139,plain,(
    ! [D_2396,A_2397,B_2398] :
      ( v5_pre_topc(D_2396,A_2397,g1_pre_topc(u1_struct_0(B_2398),u1_pre_topc(B_2398)))
      | ~ v5_pre_topc(D_2396,A_2397,B_2398)
      | ~ m1_subset_1(D_2396,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2397),u1_struct_0(g1_pre_topc(u1_struct_0(B_2398),u1_pre_topc(B_2398))))))
      | ~ v1_funct_2(D_2396,u1_struct_0(A_2397),u1_struct_0(g1_pre_topc(u1_struct_0(B_2398),u1_pre_topc(B_2398))))
      | ~ m1_subset_1(D_2396,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2397),u1_struct_0(B_2398))))
      | ~ v1_funct_2(D_2396,u1_struct_0(A_2397),u1_struct_0(B_2398))
      | ~ v1_funct_1(D_2396)
      | ~ l1_pre_topc(B_2398)
      | ~ v2_pre_topc(B_2398)
      | ~ l1_pre_topc(A_2397)
      | ~ v2_pre_topc(A_2397) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_35048,plain,(
    ! [A_2478,A_2479,B_2480] :
      ( v5_pre_topc(A_2478,A_2479,g1_pre_topc(u1_struct_0(B_2480),u1_pre_topc(B_2480)))
      | ~ v5_pre_topc(A_2478,A_2479,B_2480)
      | ~ v1_funct_2(A_2478,u1_struct_0(A_2479),u1_struct_0(g1_pre_topc(u1_struct_0(B_2480),u1_pre_topc(B_2480))))
      | ~ m1_subset_1(A_2478,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2479),u1_struct_0(B_2480))))
      | ~ v1_funct_2(A_2478,u1_struct_0(A_2479),u1_struct_0(B_2480))
      | ~ v1_funct_1(A_2478)
      | ~ l1_pre_topc(B_2480)
      | ~ v2_pre_topc(B_2480)
      | ~ l1_pre_topc(A_2479)
      | ~ v2_pre_topc(A_2479)
      | ~ r1_tarski(A_2478,k2_zfmisc_1(u1_struct_0(A_2479),u1_struct_0(g1_pre_topc(u1_struct_0(B_2480),u1_pre_topc(B_2480))))) ) ),
    inference(resolution,[status(thm)],[c_18,c_34139])).

tff(c_35657,plain,(
    ! [A_2520,B_2521] :
      ( v5_pre_topc(k2_zfmisc_1(u1_struct_0(A_2520),u1_struct_0(g1_pre_topc(u1_struct_0(B_2521),u1_pre_topc(B_2521)))),A_2520,g1_pre_topc(u1_struct_0(B_2521),u1_pre_topc(B_2521)))
      | ~ v5_pre_topc(k2_zfmisc_1(u1_struct_0(A_2520),u1_struct_0(g1_pre_topc(u1_struct_0(B_2521),u1_pre_topc(B_2521)))),A_2520,B_2521)
      | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(A_2520),u1_struct_0(g1_pre_topc(u1_struct_0(B_2521),u1_pre_topc(B_2521)))),u1_struct_0(A_2520),u1_struct_0(g1_pre_topc(u1_struct_0(B_2521),u1_pre_topc(B_2521))))
      | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(A_2520),u1_struct_0(g1_pre_topc(u1_struct_0(B_2521),u1_pre_topc(B_2521)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2520),u1_struct_0(B_2521))))
      | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(A_2520),u1_struct_0(g1_pre_topc(u1_struct_0(B_2521),u1_pre_topc(B_2521)))),u1_struct_0(A_2520),u1_struct_0(B_2521))
      | ~ v1_funct_1(k2_zfmisc_1(u1_struct_0(A_2520),u1_struct_0(g1_pre_topc(u1_struct_0(B_2521),u1_pre_topc(B_2521)))))
      | ~ l1_pre_topc(B_2521)
      | ~ v2_pre_topc(B_2521)
      | ~ l1_pre_topc(A_2520)
      | ~ v2_pre_topc(A_2520) ) ),
    inference(resolution,[status(thm)],[c_6,c_35048])).

tff(c_35675,plain,(
    ! [B_2521] :
      ( v5_pre_topc(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0(B_2521),u1_pre_topc(B_2521)))),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0(B_2521),u1_pre_topc(B_2521)))
      | ~ v5_pre_topc(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0(B_2521),u1_pre_topc(B_2521)))),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_2521)
      | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0(B_2521),u1_pre_topc(B_2521)))),'#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(B_2521),u1_pre_topc(B_2521))))
      | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0(B_2521),u1_pre_topc(B_2521)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_2521))))
      | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0(B_2521),u1_pre_topc(B_2521)))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_2521))
      | ~ v1_funct_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0(B_2521),u1_pre_topc(B_2521)))))
      | ~ l1_pre_topc(B_2521)
      | ~ v2_pre_topc(B_2521)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34606,c_35657])).

tff(c_35751,plain,(
    ! [B_2524] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0(B_2524),u1_pre_topc(B_2524)))
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_2524)
      | ~ l1_pre_topc(B_2524)
      | ~ v2_pre_topc(B_2524) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35574,c_35275,c_80,c_32270,c_34606,c_32244,c_32270,c_34606,c_34606,c_32269,c_32270,c_34606,c_34606,c_32244,c_32270,c_34606,c_32270,c_34606,c_32270,c_34606,c_35675])).

tff(c_35760,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_34444,c_35751])).

tff(c_35765,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_35760])).

tff(c_35766,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_34447,c_35765])).

tff(c_35789,plain,
    ( ~ v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_35617,c_35766])).

tff(c_35793,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_34448,c_34444,c_27444,c_35789])).

tff(c_35794,plain,(
    u1_struct_0('#skF_1') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_34443])).

tff(c_35801,plain,(
    ~ v1_partfun1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35794,c_27647])).

tff(c_35808,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32253,c_35801])).

tff(c_35809,plain,(
    u1_struct_0('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_27630])).

tff(c_35821,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35809,c_78])).

tff(c_35819,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35809,c_76])).

tff(c_35999,plain,(
    ! [A_2528,B_2529,C_2530] :
      ( k1_relset_1(A_2528,B_2529,C_2530) = k1_relat_1(C_2530)
      | ~ m1_subset_1(C_2530,k1_zfmisc_1(k2_zfmisc_1(A_2528,B_2529))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_36021,plain,(
    k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_35819,c_35999])).

tff(c_45967,plain,(
    ! [B_3097,A_3098,C_3099] :
      ( k1_xboole_0 = B_3097
      | k1_relset_1(A_3098,B_3097,C_3099) = A_3098
      | ~ v1_funct_2(C_3099,A_3098,B_3097)
      | ~ m1_subset_1(C_3099,k1_zfmisc_1(k2_zfmisc_1(A_3098,B_3097))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_45973,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0
    | k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') = u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(resolution,[status(thm)],[c_35819,c_45967])).

tff(c_45993,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35821,c_36021,c_45973])).

tff(c_46217,plain,(
    u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_45993])).

tff(c_35816,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35809,c_176])).

tff(c_46220,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46217,c_35816])).

tff(c_35820,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35809,c_103])).

tff(c_35818,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35809,c_107])).

tff(c_46223,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46217,c_35821])).

tff(c_35817,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35809,c_193])).

tff(c_46194,plain,(
    ! [D_3128,A_3129,B_3130] :
      ( v5_pre_topc(D_3128,g1_pre_topc(u1_struct_0(A_3129),u1_pre_topc(A_3129)),B_3130)
      | ~ v5_pre_topc(D_3128,A_3129,B_3130)
      | ~ m1_subset_1(D_3128,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_3129),u1_pre_topc(A_3129))),u1_struct_0(B_3130))))
      | ~ v1_funct_2(D_3128,u1_struct_0(g1_pre_topc(u1_struct_0(A_3129),u1_pre_topc(A_3129))),u1_struct_0(B_3130))
      | ~ m1_subset_1(D_3128,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3129),u1_struct_0(B_3130))))
      | ~ v1_funct_2(D_3128,u1_struct_0(A_3129),u1_struct_0(B_3130))
      | ~ v1_funct_1(D_3128)
      | ~ l1_pre_topc(B_3130)
      | ~ v2_pre_topc(B_3130)
      | ~ l1_pre_topc(A_3129)
      | ~ v2_pre_topc(A_3129) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_47506,plain,(
    ! [A_3215,A_3216,B_3217] :
      ( v5_pre_topc(A_3215,g1_pre_topc(u1_struct_0(A_3216),u1_pre_topc(A_3216)),B_3217)
      | ~ v5_pre_topc(A_3215,A_3216,B_3217)
      | ~ v1_funct_2(A_3215,u1_struct_0(g1_pre_topc(u1_struct_0(A_3216),u1_pre_topc(A_3216))),u1_struct_0(B_3217))
      | ~ m1_subset_1(A_3215,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3216),u1_struct_0(B_3217))))
      | ~ v1_funct_2(A_3215,u1_struct_0(A_3216),u1_struct_0(B_3217))
      | ~ v1_funct_1(A_3215)
      | ~ l1_pre_topc(B_3217)
      | ~ v2_pre_topc(B_3217)
      | ~ l1_pre_topc(A_3216)
      | ~ v2_pre_topc(A_3216)
      | ~ r1_tarski(A_3215,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_3216),u1_pre_topc(A_3216))),u1_struct_0(B_3217))) ) ),
    inference(resolution,[status(thm)],[c_18,c_46194])).

tff(c_47515,plain,(
    ! [A_3215,B_3217] :
      ( v5_pre_topc(A_3215,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_3217)
      | ~ v5_pre_topc(A_3215,'#skF_1',B_3217)
      | ~ v1_funct_2(A_3215,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_3217))
      | ~ m1_subset_1(A_3215,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_3217))))
      | ~ v1_funct_2(A_3215,u1_struct_0('#skF_1'),u1_struct_0(B_3217))
      | ~ v1_funct_1(A_3215)
      | ~ l1_pre_topc(B_3217)
      | ~ v2_pre_topc(B_3217)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r1_tarski(A_3215,k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(B_3217))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35809,c_47506])).

tff(c_47780,plain,(
    ! [A_3229,B_3230] :
      ( v5_pre_topc(A_3229,g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),B_3230)
      | ~ v5_pre_topc(A_3229,'#skF_1',B_3230)
      | ~ m1_subset_1(A_3229,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_3230))))
      | ~ v1_funct_2(A_3229,k1_relat_1('#skF_4'),u1_struct_0(B_3230))
      | ~ v1_funct_1(A_3229)
      | ~ l1_pre_topc(B_3230)
      | ~ v2_pre_topc(B_3230)
      | ~ r1_tarski(A_3229,k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_3230))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46217,c_94,c_92,c_35809,c_35809,c_46217,c_35809,c_35809,c_47515])).

tff(c_47789,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | ~ r1_tarski('#skF_4',k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_35818,c_47780])).

tff(c_47809,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35817,c_90,c_88,c_80,c_35820,c_27444,c_47789])).

tff(c_35825,plain,
    ( v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_35809,c_62])).

tff(c_35841,plain,(
    v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_35825])).

tff(c_35834,plain,
    ( l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_35809,c_473])).

tff(c_35847,plain,(
    l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_35834])).

tff(c_46345,plain,(
    ! [D_3131,A_3132,B_3133] :
      ( v5_pre_topc(D_3131,A_3132,g1_pre_topc(u1_struct_0(B_3133),u1_pre_topc(B_3133)))
      | ~ v5_pre_topc(D_3131,A_3132,B_3133)
      | ~ m1_subset_1(D_3131,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3132),u1_struct_0(g1_pre_topc(u1_struct_0(B_3133),u1_pre_topc(B_3133))))))
      | ~ v1_funct_2(D_3131,u1_struct_0(A_3132),u1_struct_0(g1_pre_topc(u1_struct_0(B_3133),u1_pre_topc(B_3133))))
      | ~ m1_subset_1(D_3131,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3132),u1_struct_0(B_3133))))
      | ~ v1_funct_2(D_3131,u1_struct_0(A_3132),u1_struct_0(B_3133))
      | ~ v1_funct_1(D_3131)
      | ~ l1_pre_topc(B_3133)
      | ~ v2_pre_topc(B_3133)
      | ~ l1_pre_topc(A_3132)
      | ~ v2_pre_topc(A_3132) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_47822,plain,(
    ! [A_3231,A_3232,B_3233] :
      ( v5_pre_topc(A_3231,A_3232,g1_pre_topc(u1_struct_0(B_3233),u1_pre_topc(B_3233)))
      | ~ v5_pre_topc(A_3231,A_3232,B_3233)
      | ~ v1_funct_2(A_3231,u1_struct_0(A_3232),u1_struct_0(g1_pre_topc(u1_struct_0(B_3233),u1_pre_topc(B_3233))))
      | ~ m1_subset_1(A_3231,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3232),u1_struct_0(B_3233))))
      | ~ v1_funct_2(A_3231,u1_struct_0(A_3232),u1_struct_0(B_3233))
      | ~ v1_funct_1(A_3231)
      | ~ l1_pre_topc(B_3233)
      | ~ v2_pre_topc(B_3233)
      | ~ l1_pre_topc(A_3232)
      | ~ v2_pre_topc(A_3232)
      | ~ r1_tarski(A_3231,k2_zfmisc_1(u1_struct_0(A_3232),u1_struct_0(g1_pre_topc(u1_struct_0(B_3233),u1_pre_topc(B_3233))))) ) ),
    inference(resolution,[status(thm)],[c_18,c_46345])).

tff(c_47825,plain,(
    ! [A_3231,B_3233] :
      ( v5_pre_topc(A_3231,g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0(B_3233),u1_pre_topc(B_3233)))
      | ~ v5_pre_topc(A_3231,g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),B_3233)
      | ~ v1_funct_2(A_3231,u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0(B_3233),u1_pre_topc(B_3233))))
      | ~ m1_subset_1(A_3231,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(B_3233))))
      | ~ v1_funct_2(A_3231,u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(B_3233))
      | ~ v1_funct_1(A_3231)
      | ~ l1_pre_topc(B_3233)
      | ~ v2_pre_topc(B_3233)
      | ~ l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))
      | ~ v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))
      | ~ r1_tarski(A_3231,k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0(B_3233),u1_pre_topc(B_3233))))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46217,c_47822])).

tff(c_48788,plain,(
    ! [A_3274,B_3275] :
      ( v5_pre_topc(A_3274,g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0(B_3275),u1_pre_topc(B_3275)))
      | ~ v5_pre_topc(A_3274,g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),B_3275)
      | ~ v1_funct_2(A_3274,k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0(B_3275),u1_pre_topc(B_3275))))
      | ~ m1_subset_1(A_3274,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_3275))))
      | ~ v1_funct_2(A_3274,k1_relat_1('#skF_4'),u1_struct_0(B_3275))
      | ~ v1_funct_1(A_3274)
      | ~ l1_pre_topc(B_3275)
      | ~ v2_pre_topc(B_3275)
      | ~ r1_tarski(A_3274,k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0(B_3275),u1_pre_topc(B_3275))))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35841,c_35847,c_46217,c_46217,c_46217,c_47825])).

tff(c_35813,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35809,c_27470])).

tff(c_48813,plain,
    ( ~ v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | ~ r1_tarski('#skF_4',k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))) ),
    inference(resolution,[status(thm)],[c_48788,c_35813])).

tff(c_48837,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46220,c_90,c_88,c_80,c_35820,c_35818,c_46223,c_47809,c_48813])).

tff(c_48838,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_45993])).

tff(c_48842,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48838,c_35816])).

tff(c_48847,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_48842])).

tff(c_48914,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_48847,c_168])).

tff(c_48961,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_4',B_4) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48914,c_48914,c_12])).

tff(c_48963,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48914,c_48914,c_24])).

tff(c_46137,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2')) = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35809,c_35809,c_196])).

tff(c_46138,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_46137])).

tff(c_49012,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_4',u1_struct_0('#skF_2')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48963,c_46138])).

tff(c_49629,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_48961,c_49012])).

tff(c_49630,plain,(
    k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_46137])).

tff(c_49682,plain,
    ( u1_struct_0('#skF_2') = k1_xboole_0
    | k1_relat_1('#skF_4') = k1_xboole_0
    | k1_xboole_0 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_49630,c_8])).

tff(c_49796,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_49682])).

tff(c_49633,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49630,c_35818])).

tff(c_52098,plain,(
    u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_45993])).

tff(c_51999,plain,(
    ! [D_3447,A_3448,B_3449] :
      ( v5_pre_topc(D_3447,g1_pre_topc(u1_struct_0(A_3448),u1_pre_topc(A_3448)),B_3449)
      | ~ v5_pre_topc(D_3447,A_3448,B_3449)
      | ~ m1_subset_1(D_3447,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_3448),u1_pre_topc(A_3448))),u1_struct_0(B_3449))))
      | ~ v1_funct_2(D_3447,u1_struct_0(g1_pre_topc(u1_struct_0(A_3448),u1_pre_topc(A_3448))),u1_struct_0(B_3449))
      | ~ m1_subset_1(D_3447,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3448),u1_struct_0(B_3449))))
      | ~ v1_funct_2(D_3447,u1_struct_0(A_3448),u1_struct_0(B_3449))
      | ~ v1_funct_1(D_3447)
      | ~ l1_pre_topc(B_3449)
      | ~ v2_pre_topc(B_3449)
      | ~ l1_pre_topc(A_3448)
      | ~ v2_pre_topc(A_3448) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_53908,plain,(
    ! [A_3519,A_3520,B_3521] :
      ( v5_pre_topc(A_3519,g1_pre_topc(u1_struct_0(A_3520),u1_pre_topc(A_3520)),B_3521)
      | ~ v5_pre_topc(A_3519,A_3520,B_3521)
      | ~ v1_funct_2(A_3519,u1_struct_0(g1_pre_topc(u1_struct_0(A_3520),u1_pre_topc(A_3520))),u1_struct_0(B_3521))
      | ~ m1_subset_1(A_3519,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3520),u1_struct_0(B_3521))))
      | ~ v1_funct_2(A_3519,u1_struct_0(A_3520),u1_struct_0(B_3521))
      | ~ v1_funct_1(A_3519)
      | ~ l1_pre_topc(B_3521)
      | ~ v2_pre_topc(B_3521)
      | ~ l1_pre_topc(A_3520)
      | ~ v2_pre_topc(A_3520)
      | ~ r1_tarski(A_3519,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_3520),u1_pre_topc(A_3520))),u1_struct_0(B_3521))) ) ),
    inference(resolution,[status(thm)],[c_18,c_51999])).

tff(c_53917,plain,(
    ! [A_3519,B_3521] :
      ( v5_pre_topc(A_3519,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_3521)
      | ~ v5_pre_topc(A_3519,'#skF_1',B_3521)
      | ~ v1_funct_2(A_3519,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_3521))
      | ~ m1_subset_1(A_3519,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_3521))))
      | ~ v1_funct_2(A_3519,u1_struct_0('#skF_1'),u1_struct_0(B_3521))
      | ~ v1_funct_1(A_3519)
      | ~ l1_pre_topc(B_3521)
      | ~ v2_pre_topc(B_3521)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r1_tarski(A_3519,k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(B_3521))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35809,c_53908])).

tff(c_54797,plain,(
    ! [A_3566,B_3567] :
      ( v5_pre_topc(A_3566,g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),B_3567)
      | ~ v5_pre_topc(A_3566,'#skF_1',B_3567)
      | ~ m1_subset_1(A_3566,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_3567))))
      | ~ v1_funct_2(A_3566,k1_relat_1('#skF_4'),u1_struct_0(B_3567))
      | ~ v1_funct_1(A_3566)
      | ~ l1_pre_topc(B_3567)
      | ~ v2_pre_topc(B_3567)
      | ~ r1_tarski(A_3566,k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_3567))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52098,c_94,c_92,c_35809,c_35809,c_52098,c_35809,c_35809,c_53917])).

tff(c_54806,plain,(
    ! [A_3566] :
      ( v5_pre_topc(A_3566,g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),'#skF_2')
      | ~ v5_pre_topc(A_3566,'#skF_1','#skF_2')
      | ~ m1_subset_1(A_3566,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_2(A_3566,k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(A_3566)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ r1_tarski(A_3566,k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49630,c_54797])).

tff(c_54878,plain,(
    ! [A_3570] :
      ( v5_pre_topc(A_3570,g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),'#skF_2')
      | ~ v5_pre_topc(A_3570,'#skF_1','#skF_2')
      | ~ m1_subset_1(A_3570,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_2(A_3570,k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(A_3570)
      | ~ r1_tarski(A_3570,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49630,c_90,c_88,c_54806])).

tff(c_49722,plain,(
    ! [D_3321,A_3322,B_3323] :
      ( v5_pre_topc(D_3321,A_3322,g1_pre_topc(u1_struct_0(B_3323),u1_pre_topc(B_3323)))
      | ~ v5_pre_topc(D_3321,A_3322,B_3323)
      | ~ m1_subset_1(D_3321,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3322),u1_struct_0(g1_pre_topc(u1_struct_0(B_3323),u1_pre_topc(B_3323))))))
      | ~ v1_funct_2(D_3321,u1_struct_0(A_3322),u1_struct_0(g1_pre_topc(u1_struct_0(B_3323),u1_pre_topc(B_3323))))
      | ~ m1_subset_1(D_3321,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3322),u1_struct_0(B_3323))))
      | ~ v1_funct_2(D_3321,u1_struct_0(A_3322),u1_struct_0(B_3323))
      | ~ v1_funct_1(D_3321)
      | ~ l1_pre_topc(B_3323)
      | ~ v2_pre_topc(B_3323)
      | ~ l1_pre_topc(A_3322)
      | ~ v2_pre_topc(A_3322) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_49725,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))
    | ~ v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_35819,c_49722])).

tff(c_49742,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35841,c_35847,c_90,c_88,c_80,c_35821,c_49725])).

tff(c_49743,plain,
    ( ~ v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_35813,c_49742])).

tff(c_53169,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35820,c_52098,c_49633,c_49630,c_52098,c_49743])).

tff(c_54891,plain,
    ( ~ v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4'))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_54878,c_53169])).

tff(c_54902,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_80,c_35820,c_49633,c_27444,c_54891])).

tff(c_54903,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_45993])).

tff(c_50034,plain,(
    u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_45993])).

tff(c_49967,plain,(
    ! [D_3340,A_3341,B_3342] :
      ( v5_pre_topc(D_3340,g1_pre_topc(u1_struct_0(A_3341),u1_pre_topc(A_3341)),B_3342)
      | ~ v5_pre_topc(D_3340,A_3341,B_3342)
      | ~ m1_subset_1(D_3340,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_3341),u1_pre_topc(A_3341))),u1_struct_0(B_3342))))
      | ~ v1_funct_2(D_3340,u1_struct_0(g1_pre_topc(u1_struct_0(A_3341),u1_pre_topc(A_3341))),u1_struct_0(B_3342))
      | ~ m1_subset_1(D_3340,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3341),u1_struct_0(B_3342))))
      | ~ v1_funct_2(D_3340,u1_struct_0(A_3341),u1_struct_0(B_3342))
      | ~ v1_funct_1(D_3340)
      | ~ l1_pre_topc(B_3342)
      | ~ v2_pre_topc(B_3342)
      | ~ l1_pre_topc(A_3341)
      | ~ v2_pre_topc(A_3341) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_51616,plain,(
    ! [A_3426,A_3427,B_3428] :
      ( v5_pre_topc(A_3426,g1_pre_topc(u1_struct_0(A_3427),u1_pre_topc(A_3427)),B_3428)
      | ~ v5_pre_topc(A_3426,A_3427,B_3428)
      | ~ v1_funct_2(A_3426,u1_struct_0(g1_pre_topc(u1_struct_0(A_3427),u1_pre_topc(A_3427))),u1_struct_0(B_3428))
      | ~ m1_subset_1(A_3426,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3427),u1_struct_0(B_3428))))
      | ~ v1_funct_2(A_3426,u1_struct_0(A_3427),u1_struct_0(B_3428))
      | ~ v1_funct_1(A_3426)
      | ~ l1_pre_topc(B_3428)
      | ~ v2_pre_topc(B_3428)
      | ~ l1_pre_topc(A_3427)
      | ~ v2_pre_topc(A_3427)
      | ~ r1_tarski(A_3426,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_3427),u1_pre_topc(A_3427))),u1_struct_0(B_3428))) ) ),
    inference(resolution,[status(thm)],[c_18,c_49967])).

tff(c_51625,plain,(
    ! [A_3426,B_3428] :
      ( v5_pre_topc(A_3426,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_3428)
      | ~ v5_pre_topc(A_3426,'#skF_1',B_3428)
      | ~ v1_funct_2(A_3426,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_3428))
      | ~ m1_subset_1(A_3426,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_3428))))
      | ~ v1_funct_2(A_3426,u1_struct_0('#skF_1'),u1_struct_0(B_3428))
      | ~ v1_funct_1(A_3426)
      | ~ l1_pre_topc(B_3428)
      | ~ v2_pre_topc(B_3428)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r1_tarski(A_3426,k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(B_3428))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35809,c_51616])).

tff(c_51827,plain,(
    ! [A_3438,B_3439] :
      ( v5_pre_topc(A_3438,g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),B_3439)
      | ~ v5_pre_topc(A_3438,'#skF_1',B_3439)
      | ~ m1_subset_1(A_3438,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_3439))))
      | ~ v1_funct_2(A_3438,k1_relat_1('#skF_4'),u1_struct_0(B_3439))
      | ~ v1_funct_1(A_3438)
      | ~ l1_pre_topc(B_3439)
      | ~ v2_pre_topc(B_3439)
      | ~ r1_tarski(A_3438,k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_3439))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50034,c_94,c_92,c_35809,c_35809,c_50034,c_35809,c_35809,c_51625])).

tff(c_51836,plain,(
    ! [A_3438] :
      ( v5_pre_topc(A_3438,g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),'#skF_2')
      | ~ v5_pre_topc(A_3438,'#skF_1','#skF_2')
      | ~ m1_subset_1(A_3438,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_2(A_3438,k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(A_3438)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ r1_tarski(A_3438,k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49630,c_51827])).

tff(c_51922,plain,(
    ! [A_3442] :
      ( v5_pre_topc(A_3442,g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),'#skF_2')
      | ~ v5_pre_topc(A_3442,'#skF_1','#skF_2')
      | ~ m1_subset_1(A_3442,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_2(A_3442,k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(A_3442)
      | ~ r1_tarski(A_3442,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49630,c_90,c_88,c_51836])).

tff(c_51149,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35820,c_50034,c_49633,c_49630,c_50034,c_49743])).

tff(c_51929,plain,
    ( ~ v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4'))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_51922,c_51149])).

tff(c_51936,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_80,c_35820,c_49633,c_27444,c_51929])).

tff(c_51937,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_45993])).

tff(c_49918,plain,
    ( k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35809,c_35809,c_246])).

tff(c_49919,plain,(
    ~ r1_tarski(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_49918])).

tff(c_51941,plain,(
    ~ r1_tarski(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),k1_xboole_0),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51937,c_49919])).

tff(c_51950,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_10,c_51941])).

tff(c_51951,plain,(
    k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_49918])).

tff(c_54905,plain,(
    k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),k1_xboole_0) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54903,c_51951])).

tff(c_55036,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_54905,c_10])).

tff(c_55049,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49796,c_55036])).

tff(c_55051,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_49682])).

tff(c_55095,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_55051,c_55051,c_24])).

tff(c_55172,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55095,c_35813])).

tff(c_55093,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_4',B_4) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_55051,c_55051,c_12])).

tff(c_56892,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = '#skF_4'
    | u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_55095,c_55095,c_55051,c_45993])).

tff(c_56893,plain,(
    u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))) = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_56892])).

tff(c_55191,plain,(
    u1_struct_0('#skF_1') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_55095,c_35809])).

tff(c_36013,plain,(
    ! [A_2528,B_2529] : k1_relset_1(A_2528,B_2529,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_35999])).

tff(c_36024,plain,(
    ! [A_2528,B_2529] : k1_relset_1(A_2528,B_2529,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_36013])).

tff(c_36216,plain,(
    ! [C_2559,B_2560] :
      ( v1_funct_2(C_2559,k1_xboole_0,B_2560)
      | k1_relset_1(k1_xboole_0,B_2560,C_2559) != k1_xboole_0
      | ~ m1_subset_1(C_2559,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_44])).

tff(c_36222,plain,(
    ! [B_2560] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_2560)
      | k1_relset_1(k1_xboole_0,B_2560,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14,c_36216])).

tff(c_36226,plain,(
    ! [B_2560] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_2560) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36024,c_36222])).

tff(c_55062,plain,(
    ! [B_2560] : v1_funct_2('#skF_4','#skF_4',B_2560) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55051,c_55051,c_36226])).

tff(c_55092,plain,(
    ! [A_5] : m1_subset_1('#skF_4',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55051,c_14])).

tff(c_55150,plain,(
    ! [D_3572,A_3573,B_3574] :
      ( v5_pre_topc(D_3572,g1_pre_topc(u1_struct_0(A_3573),u1_pre_topc(A_3573)),B_3574)
      | ~ v5_pre_topc(D_3572,A_3573,B_3574)
      | ~ m1_subset_1(D_3572,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_3573),u1_pre_topc(A_3573))),u1_struct_0(B_3574))))
      | ~ v1_funct_2(D_3572,u1_struct_0(g1_pre_topc(u1_struct_0(A_3573),u1_pre_topc(A_3573))),u1_struct_0(B_3574))
      | ~ m1_subset_1(D_3572,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3573),u1_struct_0(B_3574))))
      | ~ v1_funct_2(D_3572,u1_struct_0(A_3573),u1_struct_0(B_3574))
      | ~ v1_funct_1(D_3572)
      | ~ l1_pre_topc(B_3574)
      | ~ v2_pre_topc(B_3574)
      | ~ l1_pre_topc(A_3573)
      | ~ v2_pre_topc(A_3573) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_57180,plain,(
    ! [A_3766,A_3767,B_3768] :
      ( v5_pre_topc(A_3766,g1_pre_topc(u1_struct_0(A_3767),u1_pre_topc(A_3767)),B_3768)
      | ~ v5_pre_topc(A_3766,A_3767,B_3768)
      | ~ v1_funct_2(A_3766,u1_struct_0(g1_pre_topc(u1_struct_0(A_3767),u1_pre_topc(A_3767))),u1_struct_0(B_3768))
      | ~ m1_subset_1(A_3766,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3767),u1_struct_0(B_3768))))
      | ~ v1_funct_2(A_3766,u1_struct_0(A_3767),u1_struct_0(B_3768))
      | ~ v1_funct_1(A_3766)
      | ~ l1_pre_topc(B_3768)
      | ~ v2_pre_topc(B_3768)
      | ~ l1_pre_topc(A_3767)
      | ~ v2_pre_topc(A_3767)
      | ~ r1_tarski(A_3766,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_3767),u1_pre_topc(A_3767))),u1_struct_0(B_3768))) ) ),
    inference(resolution,[status(thm)],[c_18,c_55150])).

tff(c_57775,plain,(
    ! [A_3821,B_3822] :
      ( v5_pre_topc(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_3821),u1_pre_topc(A_3821))),u1_struct_0(B_3822)),g1_pre_topc(u1_struct_0(A_3821),u1_pre_topc(A_3821)),B_3822)
      | ~ v5_pre_topc(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_3821),u1_pre_topc(A_3821))),u1_struct_0(B_3822)),A_3821,B_3822)
      | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_3821),u1_pre_topc(A_3821))),u1_struct_0(B_3822)),u1_struct_0(g1_pre_topc(u1_struct_0(A_3821),u1_pre_topc(A_3821))),u1_struct_0(B_3822))
      | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_3821),u1_pre_topc(A_3821))),u1_struct_0(B_3822)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3821),u1_struct_0(B_3822))))
      | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_3821),u1_pre_topc(A_3821))),u1_struct_0(B_3822)),u1_struct_0(A_3821),u1_struct_0(B_3822))
      | ~ v1_funct_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_3821),u1_pre_topc(A_3821))),u1_struct_0(B_3822)))
      | ~ l1_pre_topc(B_3822)
      | ~ v2_pre_topc(B_3822)
      | ~ l1_pre_topc(A_3821)
      | ~ v2_pre_topc(A_3821) ) ),
    inference(resolution,[status(thm)],[c_6,c_57180])).

tff(c_57796,plain,(
    ! [B_3822] :
      ( v5_pre_topc(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_3822)),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_3822)
      | ~ v5_pre_topc(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_3822)),'#skF_1',B_3822)
      | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),u1_struct_0(B_3822)),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_3822))
      | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_3822)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_3822))))
      | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_3822)),u1_struct_0('#skF_1'),u1_struct_0(B_3822))
      | ~ v1_funct_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_3822)))
      | ~ l1_pre_topc(B_3822)
      | ~ v2_pre_topc(B_3822)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55191,c_57775])).

tff(c_57825,plain,(
    ! [B_3823] :
      ( v5_pre_topc('#skF_4',g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),B_3823)
      | ~ v5_pre_topc('#skF_4','#skF_1',B_3823)
      | ~ l1_pre_topc(B_3823)
      | ~ v2_pre_topc(B_3823) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_80,c_55093,c_56893,c_55191,c_55062,c_55093,c_56893,c_55191,c_55191,c_55092,c_55093,c_56893,c_55093,c_55191,c_55191,c_55062,c_56893,c_55093,c_56893,c_55191,c_55093,c_56893,c_55191,c_55093,c_56893,c_55191,c_55191,c_57796])).

tff(c_55186,plain,(
    v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55095,c_35841])).

tff(c_55184,plain,(
    l1_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55095,c_35847])).

tff(c_55190,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55095,c_35821])).

tff(c_27534,plain,(
    ! [B_1892,A_1893] :
      ( v1_funct_1(B_1892)
      | ~ m1_subset_1(B_1892,k1_zfmisc_1(A_1893))
      | ~ v1_funct_1(A_1893)
      | ~ v1_relat_1(A_1893) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_27558,plain,(
    ! [A_5] :
      ( v1_funct_1(k1_xboole_0)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(resolution,[status(thm)],[c_14,c_27534])).

tff(c_27560,plain,(
    ! [A_1894] :
      ( ~ v1_funct_1(A_1894)
      | ~ v1_relat_1(A_1894) ) ),
    inference(splitLeft,[status(thm)],[c_27558])).

tff(c_27569,plain,(
    ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_216,c_27560])).

tff(c_27575,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_27569])).

tff(c_27576,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_27558])).

tff(c_49739,plain,(
    ! [A_3322,B_3323] :
      ( v5_pre_topc(k1_xboole_0,A_3322,g1_pre_topc(u1_struct_0(B_3323),u1_pre_topc(B_3323)))
      | ~ v5_pre_topc(k1_xboole_0,A_3322,B_3323)
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(A_3322),u1_struct_0(g1_pre_topc(u1_struct_0(B_3323),u1_pre_topc(B_3323))))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3322),u1_struct_0(B_3323))))
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(A_3322),u1_struct_0(B_3323))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ l1_pre_topc(B_3323)
      | ~ v2_pre_topc(B_3323)
      | ~ l1_pre_topc(A_3322)
      | ~ v2_pre_topc(A_3322) ) ),
    inference(resolution,[status(thm)],[c_14,c_49722])).

tff(c_49751,plain,(
    ! [A_3322,B_3323] :
      ( v5_pre_topc(k1_xboole_0,A_3322,g1_pre_topc(u1_struct_0(B_3323),u1_pre_topc(B_3323)))
      | ~ v5_pre_topc(k1_xboole_0,A_3322,B_3323)
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(A_3322),u1_struct_0(g1_pre_topc(u1_struct_0(B_3323),u1_pre_topc(B_3323))))
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(A_3322),u1_struct_0(B_3323))
      | ~ l1_pre_topc(B_3323)
      | ~ v2_pre_topc(B_3323)
      | ~ l1_pre_topc(A_3322)
      | ~ v2_pre_topc(A_3322) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27576,c_14,c_49739])).

tff(c_56920,plain,(
    ! [A_3741,B_3742] :
      ( v5_pre_topc('#skF_4',A_3741,g1_pre_topc(u1_struct_0(B_3742),u1_pre_topc(B_3742)))
      | ~ v5_pre_topc('#skF_4',A_3741,B_3742)
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_3741),u1_struct_0(g1_pre_topc(u1_struct_0(B_3742),u1_pre_topc(B_3742))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_3741),u1_struct_0(B_3742))
      | ~ l1_pre_topc(B_3742)
      | ~ v2_pre_topc(B_3742)
      | ~ l1_pre_topc(A_3741)
      | ~ v2_pre_topc(A_3741) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55051,c_55051,c_55051,c_55051,c_49751])).

tff(c_56929,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4',g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),'#skF_2')
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | ~ l1_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')))
    | ~ v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_55190,c_56920])).

tff(c_56936,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4',g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),'#skF_2')
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55186,c_55184,c_90,c_88,c_56929])).

tff(c_57755,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4',g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55062,c_56893,c_56936])).

tff(c_57756,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_55172,c_57755])).

tff(c_57828,plain,
    ( ~ v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_57825,c_57756])).

tff(c_57838,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_27444,c_57828])).

tff(c_57839,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_56892])).

tff(c_57985,plain,
    ( r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),k1_zfmisc_1('#skF_4'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_57839,c_474])).

tff(c_58642,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_57985])).

tff(c_58645,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_473,c_58642])).

tff(c_58649,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_58645])).

tff(c_58651,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_57985])).

tff(c_57979,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_57839,c_62])).

tff(c_59029,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58651,c_57979])).

tff(c_59030,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_59029])).

tff(c_59033,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_59030])).

tff(c_59037,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_59033])).

tff(c_59039,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_59029])).

tff(c_57912,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57839,c_55190])).

tff(c_57868,plain,(
    ! [A_3828,B_3829] :
      ( v5_pre_topc('#skF_4',A_3828,g1_pre_topc(u1_struct_0(B_3829),u1_pre_topc(B_3829)))
      | ~ v5_pre_topc('#skF_4',A_3828,B_3829)
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_3828),u1_struct_0(g1_pre_topc(u1_struct_0(B_3829),u1_pre_topc(B_3829))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_3828),u1_struct_0(B_3829))
      | ~ l1_pre_topc(B_3829)
      | ~ v2_pre_topc(B_3829)
      | ~ l1_pre_topc(A_3828)
      | ~ v2_pre_topc(A_3828) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55051,c_55051,c_55051,c_55051,c_49751])).

tff(c_57871,plain,(
    ! [B_3829] :
      ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0(B_3829),u1_pre_topc(B_3829)))
      | ~ v5_pre_topc('#skF_4','#skF_1',B_3829)
      | ~ v1_funct_2('#skF_4','#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(B_3829),u1_pre_topc(B_3829))))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0(B_3829))
      | ~ l1_pre_topc(B_3829)
      | ~ v2_pre_topc(B_3829)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55191,c_57868])).

tff(c_57879,plain,(
    ! [B_3829] :
      ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0(B_3829),u1_pre_topc(B_3829)))
      | ~ v5_pre_topc('#skF_4','#skF_1',B_3829)
      | ~ l1_pre_topc(B_3829)
      | ~ v2_pre_topc(B_3829) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_55062,c_55191,c_55062,c_57871])).

tff(c_55292,plain,(
    ! [D_3577,A_3578,B_3579] :
      ( v5_pre_topc(D_3577,A_3578,B_3579)
      | ~ v5_pre_topc(D_3577,A_3578,g1_pre_topc(u1_struct_0(B_3579),u1_pre_topc(B_3579)))
      | ~ m1_subset_1(D_3577,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3578),u1_struct_0(g1_pre_topc(u1_struct_0(B_3579),u1_pre_topc(B_3579))))))
      | ~ v1_funct_2(D_3577,u1_struct_0(A_3578),u1_struct_0(g1_pre_topc(u1_struct_0(B_3579),u1_pre_topc(B_3579))))
      | ~ m1_subset_1(D_3577,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3578),u1_struct_0(B_3579))))
      | ~ v1_funct_2(D_3577,u1_struct_0(A_3578),u1_struct_0(B_3579))
      | ~ v1_funct_1(D_3577)
      | ~ l1_pre_topc(B_3579)
      | ~ v2_pre_topc(B_3579)
      | ~ l1_pre_topc(A_3578)
      | ~ v2_pre_topc(A_3578) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_58213,plain,(
    ! [A_3860,A_3861,B_3862] :
      ( v5_pre_topc(A_3860,A_3861,B_3862)
      | ~ v5_pre_topc(A_3860,A_3861,g1_pre_topc(u1_struct_0(B_3862),u1_pre_topc(B_3862)))
      | ~ v1_funct_2(A_3860,u1_struct_0(A_3861),u1_struct_0(g1_pre_topc(u1_struct_0(B_3862),u1_pre_topc(B_3862))))
      | ~ m1_subset_1(A_3860,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3861),u1_struct_0(B_3862))))
      | ~ v1_funct_2(A_3860,u1_struct_0(A_3861),u1_struct_0(B_3862))
      | ~ v1_funct_1(A_3860)
      | ~ l1_pre_topc(B_3862)
      | ~ v2_pre_topc(B_3862)
      | ~ l1_pre_topc(A_3861)
      | ~ v2_pre_topc(A_3861)
      | ~ r1_tarski(A_3860,k2_zfmisc_1(u1_struct_0(A_3861),u1_struct_0(g1_pre_topc(u1_struct_0(B_3862),u1_pre_topc(B_3862))))) ) ),
    inference(resolution,[status(thm)],[c_18,c_55292])).

tff(c_58786,plain,(
    ! [A_3906,B_3907] :
      ( v5_pre_topc(k2_zfmisc_1(u1_struct_0(A_3906),u1_struct_0(g1_pre_topc(u1_struct_0(B_3907),u1_pre_topc(B_3907)))),A_3906,B_3907)
      | ~ v5_pre_topc(k2_zfmisc_1(u1_struct_0(A_3906),u1_struct_0(g1_pre_topc(u1_struct_0(B_3907),u1_pre_topc(B_3907)))),A_3906,g1_pre_topc(u1_struct_0(B_3907),u1_pre_topc(B_3907)))
      | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(A_3906),u1_struct_0(g1_pre_topc(u1_struct_0(B_3907),u1_pre_topc(B_3907)))),u1_struct_0(A_3906),u1_struct_0(g1_pre_topc(u1_struct_0(B_3907),u1_pre_topc(B_3907))))
      | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(A_3906),u1_struct_0(g1_pre_topc(u1_struct_0(B_3907),u1_pre_topc(B_3907)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3906),u1_struct_0(B_3907))))
      | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(A_3906),u1_struct_0(g1_pre_topc(u1_struct_0(B_3907),u1_pre_topc(B_3907)))),u1_struct_0(A_3906),u1_struct_0(B_3907))
      | ~ v1_funct_1(k2_zfmisc_1(u1_struct_0(A_3906),u1_struct_0(g1_pre_topc(u1_struct_0(B_3907),u1_pre_topc(B_3907)))))
      | ~ l1_pre_topc(B_3907)
      | ~ v2_pre_topc(B_3907)
      | ~ l1_pre_topc(A_3906)
      | ~ v2_pre_topc(A_3906) ) ),
    inference(resolution,[status(thm)],[c_6,c_58213])).

tff(c_58813,plain,(
    ! [B_3907] :
      ( v5_pre_topc(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(g1_pre_topc(u1_struct_0(B_3907),u1_pre_topc(B_3907)))),'#skF_1',B_3907)
      | ~ v5_pre_topc(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(g1_pre_topc(u1_struct_0(B_3907),u1_pre_topc(B_3907)))),'#skF_1',g1_pre_topc(u1_struct_0(B_3907),u1_pre_topc(B_3907)))
      | ~ v1_funct_2(k2_zfmisc_1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(B_3907),u1_pre_topc(B_3907)))),u1_struct_0('#skF_1'),u1_struct_0(g1_pre_topc(u1_struct_0(B_3907),u1_pre_topc(B_3907))))
      | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(g1_pre_topc(u1_struct_0(B_3907),u1_pre_topc(B_3907)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_3907))))
      | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(g1_pre_topc(u1_struct_0(B_3907),u1_pre_topc(B_3907)))),u1_struct_0('#skF_1'),u1_struct_0(B_3907))
      | ~ v1_funct_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(g1_pre_topc(u1_struct_0(B_3907),u1_pre_topc(B_3907)))))
      | ~ l1_pre_topc(B_3907)
      | ~ v2_pre_topc(B_3907)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55191,c_58786])).

tff(c_58845,plain,(
    ! [B_3908] :
      ( v5_pre_topc('#skF_4','#skF_1',B_3908)
      | ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0(B_3908),u1_pre_topc(B_3908)))
      | ~ l1_pre_topc(B_3908)
      | ~ v2_pre_topc(B_3908) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_80,c_55093,c_55191,c_55062,c_55191,c_55093,c_55191,c_55092,c_55093,c_55191,c_55062,c_55191,c_55093,c_55093,c_55191,c_55093,c_55191,c_58813])).

tff(c_58851,plain,
    ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_57839,c_58845])).

tff(c_58857,plain,
    ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58651,c_58851])).

tff(c_59108,plain,
    ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59039,c_58857])).

tff(c_59109,plain,(
    ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))) ),
    inference(splitLeft,[status(thm)],[c_59108])).

tff(c_58774,plain,(
    ! [B_3905] :
      ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0(B_3905),u1_pre_topc(B_3905)))
      | ~ v5_pre_topc('#skF_4','#skF_1',B_3905)
      | ~ l1_pre_topc(B_3905)
      | ~ v2_pre_topc(B_3905) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_55062,c_55191,c_55062,c_57871])).

tff(c_58777,plain,
    ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
    | ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_57839,c_58774])).

tff(c_58782,plain,
    ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
    | ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58651,c_58777])).

tff(c_59111,plain,
    ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
    | ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59039,c_58782])).

tff(c_59112,plain,(
    ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_59109,c_59111])).

tff(c_59115,plain,
    ( ~ v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_57879,c_59112])).

tff(c_59119,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_27444,c_59115])).

tff(c_59120,plain,(
    v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_59108])).

tff(c_55153,plain,(
    ! [D_3572,B_3574] :
      ( v5_pre_topc(D_3572,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_3574)
      | ~ v5_pre_topc(D_3572,'#skF_1',B_3574)
      | ~ m1_subset_1(D_3572,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(B_3574))))
      | ~ v1_funct_2(D_3572,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_3574))
      | ~ m1_subset_1(D_3572,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_3574))))
      | ~ v1_funct_2(D_3572,u1_struct_0('#skF_1'),u1_struct_0(B_3574))
      | ~ v1_funct_1(D_3572)
      | ~ l1_pre_topc(B_3574)
      | ~ v2_pre_topc(B_3574)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35809,c_55150])).

tff(c_55162,plain,(
    ! [D_3572,B_3574] :
      ( v5_pre_topc(D_3572,g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),B_3574)
      | ~ v5_pre_topc(D_3572,'#skF_1',B_3574)
      | ~ m1_subset_1(D_3572,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(B_3574))))
      | ~ v1_funct_2(D_3572,u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(B_3574))
      | ~ m1_subset_1(D_3572,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_3574))))
      | ~ v1_funct_2(D_3572,k1_relat_1('#skF_4'),u1_struct_0(B_3574))
      | ~ v1_funct_1(D_3572)
      | ~ l1_pre_topc(B_3574)
      | ~ v2_pre_topc(B_3574) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_35809,c_35809,c_35809,c_35809,c_55153])).

tff(c_59284,plain,(
    ! [D_3934,B_3935] :
      ( v5_pre_topc(D_3934,g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),B_3935)
      | ~ v5_pre_topc(D_3934,'#skF_1',B_3935)
      | ~ m1_subset_1(D_3934,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),u1_struct_0(B_3935))))
      | ~ v1_funct_2(D_3934,u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),u1_struct_0(B_3935))
      | ~ m1_subset_1(D_3934,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_2(D_3934,'#skF_4',u1_struct_0(B_3935))
      | ~ v1_funct_1(D_3934)
      | ~ l1_pre_topc(B_3935)
      | ~ v2_pre_topc(B_3935) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55095,c_55093,c_55095,c_55095,c_55095,c_55095,c_55162])).

tff(c_59291,plain,(
    ! [B_3935] :
      ( v5_pre_topc('#skF_4',g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),B_3935)
      | ~ v5_pre_topc('#skF_4','#skF_1',B_3935)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),u1_struct_0(B_3935))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_2('#skF_4','#skF_4',u1_struct_0(B_3935))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(B_3935)
      | ~ v2_pre_topc(B_3935) ) ),
    inference(resolution,[status(thm)],[c_55092,c_59284])).

tff(c_59372,plain,(
    ! [B_3936] :
      ( v5_pre_topc('#skF_4',g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),B_3936)
      | ~ v5_pre_topc('#skF_4','#skF_1',B_3936)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),u1_struct_0(B_3936))
      | ~ l1_pre_topc(B_3936)
      | ~ v2_pre_topc(B_3936) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_55062,c_55092,c_59291])).

tff(c_59381,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),'#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_57839,c_59372])).

tff(c_59388,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59039,c_58651,c_57912,c_59120,c_59381])).

tff(c_59390,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55172,c_59388])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:33:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 18.73/10.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.24/10.86  
% 19.24/10.86  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.24/10.86  %$ v5_pre_topc > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_relat_1 > v1_pre_topc > v1_funct_1 > l1_pre_topc > k1_relset_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 19.24/10.86  
% 19.24/10.86  %Foreground sorts:
% 19.24/10.86  
% 19.24/10.86  
% 19.24/10.86  %Background operators:
% 19.24/10.86  
% 19.24/10.86  
% 19.24/10.86  %Foreground operators:
% 19.24/10.86  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 19.24/10.86  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 19.24/10.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 19.24/10.86  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 19.24/10.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 19.24/10.86  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 19.24/10.86  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 19.24/10.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 19.24/10.86  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 19.24/10.86  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 19.24/10.86  tff('#skF_2', type, '#skF_2': $i).
% 19.24/10.86  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 19.24/10.86  tff('#skF_3', type, '#skF_3': $i).
% 19.24/10.86  tff('#skF_1', type, '#skF_1': $i).
% 19.24/10.86  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 19.24/10.86  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 19.24/10.86  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 19.24/10.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 19.24/10.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 19.24/10.86  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 19.24/10.86  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 19.24/10.86  tff('#skF_4', type, '#skF_4': $i).
% 19.24/10.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 19.24/10.86  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 19.24/10.86  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 19.24/10.86  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 19.24/10.86  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 19.24/10.86  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 19.24/10.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 19.24/10.86  
% 19.24/10.93  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 19.24/10.93  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 19.24/10.93  tff(f_39, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 19.24/10.93  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 19.24/10.93  tff(f_217, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))), u1_struct_0(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))), u1_struct_0(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))) => ((C = D) => (v5_pre_topc(C, A, B) <=> v5_pre_topc(D, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)), g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_pre_topc)).
% 19.24/10.93  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 19.24/10.93  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 19.24/10.93  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 19.24/10.93  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 19.24/10.93  tff(f_111, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 19.24/10.93  tff(f_52, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 19.24/10.93  tff(f_129, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & v2_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_pre_topc)).
% 19.24/10.93  tff(f_121, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 19.24/10.93  tff(f_117, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v1_pre_topc(g1_pre_topc(A, B)) & l1_pre_topc(g1_pre_topc(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 19.24/10.93  tff(f_158, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))), u1_struct_0(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))), u1_struct_0(B))))) => ((C = D) => (v5_pre_topc(C, A, B) <=> v5_pre_topc(D, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)), B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_pre_topc)).
% 19.24/10.93  tff(f_187, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(A), u1_struct_0(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))) => ((C = D) => (v5_pre_topc(C, A, B) <=> v5_pre_topc(D, A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_pre_topc)).
% 19.24/10.93  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 19.24/10.93  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_funct_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_funct_1)).
% 19.24/10.93  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 19.24/10.93  tff(c_10, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 19.24/10.93  tff(c_14, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 19.24/10.93  tff(c_153, plain, (![A_83, B_84]: (r1_tarski(A_83, B_84) | ~m1_subset_1(A_83, k1_zfmisc_1(B_84)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 19.24/10.93  tff(c_161, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(resolution, [status(thm)], [c_14, c_153])).
% 19.24/10.93  tff(c_74, plain, ('#skF_3'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_217])).
% 19.24/10.93  tff(c_82, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_217])).
% 19.24/10.93  tff(c_107, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_82])).
% 19.24/10.93  tff(c_197, plain, (![C_89, A_90, B_91]: (v1_relat_1(C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 19.24/10.93  tff(c_216, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_107, c_197])).
% 19.24/10.93  tff(c_84, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_217])).
% 19.24/10.93  tff(c_103, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_84])).
% 19.24/10.93  tff(c_30559, plain, (![A_2122, B_2123, C_2124]: (k1_relset_1(A_2122, B_2123, C_2124)=k1_relat_1(C_2124) | ~m1_subset_1(C_2124, k1_zfmisc_1(k2_zfmisc_1(A_2122, B_2123))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 19.24/10.93  tff(c_30580, plain, (k1_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_107, c_30559])).
% 19.24/10.93  tff(c_31019, plain, (![B_2184, A_2185, C_2186]: (k1_xboole_0=B_2184 | k1_relset_1(A_2185, B_2184, C_2186)=A_2185 | ~v1_funct_2(C_2186, A_2185, B_2184) | ~m1_subset_1(C_2186, k1_zfmisc_1(k2_zfmisc_1(A_2185, B_2184))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 19.24/10.93  tff(c_31025, plain, (u1_struct_0('#skF_2')=k1_xboole_0 | k1_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4')=u1_struct_0('#skF_1') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_107, c_31019])).
% 19.24/10.93  tff(c_31042, plain, (u1_struct_0('#skF_2')=k1_xboole_0 | u1_struct_0('#skF_1')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_30580, c_31025])).
% 19.24/10.93  tff(c_31047, plain, (u1_struct_0('#skF_1')=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_31042])).
% 19.24/10.93  tff(c_383, plain, (![C_117, A_118, B_119]: (v4_relat_1(C_117, A_118) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 19.24/10.93  tff(c_404, plain, (v4_relat_1('#skF_4', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_107, c_383])).
% 19.24/10.93  tff(c_31058, plain, (v4_relat_1('#skF_4', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_31047, c_404])).
% 19.24/10.93  tff(c_52, plain, (![B_30]: (v1_partfun1(B_30, k1_relat_1(B_30)) | ~v4_relat_1(B_30, k1_relat_1(B_30)) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_111])).
% 19.24/10.93  tff(c_31112, plain, (v1_partfun1('#skF_4', k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_31058, c_52])).
% 19.24/10.93  tff(c_31119, plain, (v1_partfun1('#skF_4', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_216, c_31112])).
% 19.24/10.93  tff(c_27605, plain, (![B_1899, A_1900]: (k1_relat_1(B_1899)=A_1900 | ~v1_partfun1(B_1899, A_1900) | ~v4_relat_1(B_1899, A_1900) | ~v1_relat_1(B_1899))), inference(cnfTransformation, [status(thm)], [f_111])).
% 19.24/10.93  tff(c_27617, plain, (u1_struct_0('#skF_1')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', u1_struct_0('#skF_1')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_404, c_27605])).
% 19.24/10.93  tff(c_27630, plain, (u1_struct_0('#skF_1')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_216, c_27617])).
% 19.24/10.93  tff(c_27647, plain, (~v1_partfun1('#skF_4', u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_27630])).
% 19.24/10.93  tff(c_31054, plain, (~v1_partfun1('#skF_4', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_31047, c_27647])).
% 19.24/10.93  tff(c_31128, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_31119, c_31054])).
% 19.24/10.93  tff(c_31129, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_31042])).
% 19.24/10.93  tff(c_16, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 19.24/10.93  tff(c_193, plain, (r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_107, c_16])).
% 19.24/10.93  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 19.24/10.93  tff(c_196, plain, (k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))='#skF_4' | ~r1_tarski(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')), '#skF_4')), inference(resolution, [status(thm)], [c_193, c_2])).
% 19.24/10.93  tff(c_30729, plain, (~r1_tarski(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')), '#skF_4')), inference(splitLeft, [status(thm)], [c_196])).
% 19.24/10.93  tff(c_31134, plain, (~r1_tarski(k2_zfmisc_1(u1_struct_0('#skF_1'), k1_xboole_0), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_31129, c_30729])).
% 19.24/10.93  tff(c_31147, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_161, c_10, c_31134])).
% 19.24/10.93  tff(c_31148, plain, (k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))='#skF_4'), inference(splitRight, [status(thm)], [c_196])).
% 19.24/10.93  tff(c_8, plain, (![B_4, A_3]: (k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 19.24/10.93  tff(c_31191, plain, (u1_struct_0('#skF_2')=k1_xboole_0 | u1_struct_0('#skF_1')=k1_xboole_0 | k1_xboole_0!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_31148, c_8])).
% 19.24/10.93  tff(c_31405, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_31191])).
% 19.24/10.93  tff(c_18, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 19.24/10.93  tff(c_30661, plain, (![A_2138, B_2139, A_2140]: (k1_relset_1(A_2138, B_2139, A_2140)=k1_relat_1(A_2140) | ~r1_tarski(A_2140, k2_zfmisc_1(A_2138, B_2139)))), inference(resolution, [status(thm)], [c_18, c_30559])).
% 19.24/10.93  tff(c_30688, plain, (![A_2138, B_2139]: (k1_relset_1(A_2138, B_2139, k2_zfmisc_1(A_2138, B_2139))=k1_relat_1(k2_zfmisc_1(A_2138, B_2139)))), inference(resolution, [status(thm)], [c_6, c_30661])).
% 19.24/10.93  tff(c_31346, plain, (![B_2196, A_2197, C_2198]: (k1_xboole_0=B_2196 | k1_relset_1(A_2197, B_2196, C_2198)=A_2197 | ~v1_funct_2(C_2198, A_2197, B_2196) | ~m1_subset_1(C_2198, k1_zfmisc_1(k2_zfmisc_1(A_2197, B_2196))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 19.24/10.93  tff(c_31823, plain, (![B_2246, A_2247, A_2248]: (k1_xboole_0=B_2246 | k1_relset_1(A_2247, B_2246, A_2248)=A_2247 | ~v1_funct_2(A_2248, A_2247, B_2246) | ~r1_tarski(A_2248, k2_zfmisc_1(A_2247, B_2246)))), inference(resolution, [status(thm)], [c_18, c_31346])).
% 19.24/10.93  tff(c_31843, plain, (![B_2246, A_2247]: (k1_xboole_0=B_2246 | k1_relset_1(A_2247, B_2246, k2_zfmisc_1(A_2247, B_2246))=A_2247 | ~v1_funct_2(k2_zfmisc_1(A_2247, B_2246), A_2247, B_2246))), inference(resolution, [status(thm)], [c_6, c_31823])).
% 19.24/10.93  tff(c_31849, plain, (![B_2249, A_2250]: (k1_xboole_0=B_2249 | k1_relat_1(k2_zfmisc_1(A_2250, B_2249))=A_2250 | ~v1_funct_2(k2_zfmisc_1(A_2250, B_2249), A_2250, B_2249))), inference(demodulation, [status(thm), theory('equality')], [c_30688, c_31843])).
% 19.24/10.93  tff(c_31873, plain, (u1_struct_0('#skF_2')=k1_xboole_0 | k1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))=u1_struct_0('#skF_1') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_31148, c_31849])).
% 19.24/10.93  tff(c_31898, plain, (u1_struct_0('#skF_2')=k1_xboole_0 | u1_struct_0('#skF_1')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_31148, c_31873])).
% 19.24/10.93  tff(c_31905, plain, (u1_struct_0('#skF_1')=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_31898])).
% 19.24/10.93  tff(c_31921, plain, (~v1_partfun1('#skF_4', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_31905, c_27647])).
% 19.24/10.93  tff(c_31924, plain, (v4_relat_1('#skF_4', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_31905, c_404])).
% 19.24/10.93  tff(c_32019, plain, (v1_partfun1('#skF_4', k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_31924, c_52])).
% 19.24/10.93  tff(c_32026, plain, (v1_partfun1('#skF_4', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_216, c_32019])).
% 19.24/10.93  tff(c_32033, plain, $false, inference(negUnitSimplification, [status(thm)], [c_31921, c_32026])).
% 19.24/10.93  tff(c_32034, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_31898])).
% 19.24/10.93  tff(c_32045, plain, (k2_zfmisc_1(u1_struct_0('#skF_1'), k1_xboole_0)='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_32034, c_31148])).
% 19.24/10.93  tff(c_32185, plain, (k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_32045, c_10])).
% 19.24/10.93  tff(c_32206, plain, $false, inference(negUnitSimplification, [status(thm)], [c_31405, c_32185])).
% 19.24/10.93  tff(c_32208, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_31191])).
% 19.24/10.93  tff(c_219, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_197])).
% 19.24/10.93  tff(c_407, plain, (![A_118]: (v4_relat_1(k1_xboole_0, A_118))), inference(resolution, [status(thm)], [c_14, c_383])).
% 19.24/10.93  tff(c_24, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_52])).
% 19.24/10.93  tff(c_27490, plain, (![B_1881]: (v1_partfun1(B_1881, k1_relat_1(B_1881)) | ~v4_relat_1(B_1881, k1_relat_1(B_1881)) | ~v1_relat_1(B_1881))), inference(cnfTransformation, [status(thm)], [f_111])).
% 19.24/10.93  tff(c_27501, plain, (v1_partfun1(k1_xboole_0, k1_relat_1(k1_xboole_0)) | ~v4_relat_1(k1_xboole_0, k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_24, c_27490])).
% 19.24/10.93  tff(c_27507, plain, (v1_partfun1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_219, c_407, c_24, c_27501])).
% 19.24/10.93  tff(c_32253, plain, (v1_partfun1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32208, c_32208, c_27507])).
% 19.24/10.93  tff(c_90, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_217])).
% 19.24/10.93  tff(c_88, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_217])).
% 19.24/10.93  tff(c_32207, plain, (u1_struct_0('#skF_1')=k1_xboole_0 | u1_struct_0('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_31191])).
% 19.24/10.93  tff(c_34443, plain, (u1_struct_0('#skF_1')='#skF_4' | u1_struct_0('#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_32208, c_32208, c_32207])).
% 19.24/10.93  tff(c_34444, plain, (u1_struct_0('#skF_2')='#skF_4'), inference(splitLeft, [status(thm)], [c_34443])).
% 19.24/10.93  tff(c_34448, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34444, c_103])).
% 19.24/10.93  tff(c_102, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_217])).
% 19.24/10.93  tff(c_104, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_102])).
% 19.24/10.93  tff(c_489, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_104])).
% 19.24/10.93  tff(c_96, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_217])).
% 19.24/10.93  tff(c_106, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_96])).
% 19.24/10.93  tff(c_551, plain, (~v5_pre_topc('#skF_4', '#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_106])).
% 19.24/10.93  tff(c_62, plain, (![A_34]: (v2_pre_topc(g1_pre_topc(u1_struct_0(A_34), u1_pre_topc(A_34))) | ~l1_pre_topc(A_34) | ~v2_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_129])).
% 19.24/10.93  tff(c_466, plain, (![A_132]: (m1_subset_1(u1_pre_topc(A_132), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_132)))) | ~l1_pre_topc(A_132))), inference(cnfTransformation, [status(thm)], [f_121])).
% 19.24/10.93  tff(c_56, plain, (![A_31, B_32]: (l1_pre_topc(g1_pre_topc(A_31, B_32)) | ~m1_subset_1(B_32, k1_zfmisc_1(k1_zfmisc_1(A_31))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 19.24/10.93  tff(c_473, plain, (![A_132]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_132), u1_pre_topc(A_132))) | ~l1_pre_topc(A_132))), inference(resolution, [status(thm)], [c_466, c_56])).
% 19.24/10.93  tff(c_80, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_217])).
% 19.24/10.93  tff(c_733, plain, (![A_176, B_177, C_178]: (k1_relset_1(A_176, B_177, C_178)=k1_relat_1(C_178) | ~m1_subset_1(C_178, k1_zfmisc_1(k2_zfmisc_1(A_176, B_177))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 19.24/10.93  tff(c_754, plain, (k1_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_107, c_733])).
% 19.24/10.93  tff(c_3647, plain, (![B_409, A_410, C_411]: (k1_xboole_0=B_409 | k1_relset_1(A_410, B_409, C_411)=A_410 | ~v1_funct_2(C_411, A_410, B_409) | ~m1_subset_1(C_411, k1_zfmisc_1(k2_zfmisc_1(A_410, B_409))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 19.24/10.93  tff(c_3653, plain, (u1_struct_0('#skF_2')=k1_xboole_0 | k1_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4')=u1_struct_0('#skF_1') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_107, c_3647])).
% 19.24/10.93  tff(c_3670, plain, (u1_struct_0('#skF_2')=k1_xboole_0 | u1_struct_0('#skF_1')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_754, c_3653])).
% 19.24/10.93  tff(c_3675, plain, (u1_struct_0('#skF_1')=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_3670])).
% 19.24/10.93  tff(c_3686, plain, (v4_relat_1('#skF_4', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3675, c_404])).
% 19.24/10.93  tff(c_3740, plain, (v1_partfun1('#skF_4', k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_3686, c_52])).
% 19.24/10.93  tff(c_3747, plain, (v1_partfun1('#skF_4', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_216, c_3740])).
% 19.24/10.93  tff(c_647, plain, (![B_162, A_163]: (k1_relat_1(B_162)=A_163 | ~v1_partfun1(B_162, A_163) | ~v4_relat_1(B_162, A_163) | ~v1_relat_1(B_162))), inference(cnfTransformation, [status(thm)], [f_111])).
% 19.24/10.93  tff(c_659, plain, (u1_struct_0('#skF_1')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', u1_struct_0('#skF_1')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_404, c_647])).
% 19.24/10.93  tff(c_672, plain, (u1_struct_0('#skF_1')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_216, c_659])).
% 19.24/10.93  tff(c_689, plain, (~v1_partfun1('#skF_4', u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_672])).
% 19.24/10.93  tff(c_3682, plain, (~v1_partfun1('#skF_4', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3675, c_689])).
% 19.24/10.93  tff(c_3756, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3747, c_3682])).
% 19.24/10.93  tff(c_3757, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_3670])).
% 19.24/10.93  tff(c_3378, plain, (~r1_tarski(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')), '#skF_4')), inference(splitLeft, [status(thm)], [c_196])).
% 19.24/10.93  tff(c_3762, plain, (~r1_tarski(k2_zfmisc_1(u1_struct_0('#skF_1'), k1_xboole_0), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3757, c_3378])).
% 19.24/10.93  tff(c_3775, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_161, c_10, c_3762])).
% 19.24/10.93  tff(c_3776, plain, (k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))='#skF_4'), inference(splitRight, [status(thm)], [c_196])).
% 19.24/10.93  tff(c_3819, plain, (u1_struct_0('#skF_2')=k1_xboole_0 | u1_struct_0('#skF_1')=k1_xboole_0 | k1_xboole_0!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_3776, c_8])).
% 19.24/10.93  tff(c_4034, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_3819])).
% 19.24/10.93  tff(c_816, plain, (![A_189, B_190, A_191]: (k1_relset_1(A_189, B_190, A_191)=k1_relat_1(A_191) | ~r1_tarski(A_191, k2_zfmisc_1(A_189, B_190)))), inference(resolution, [status(thm)], [c_18, c_733])).
% 19.24/10.93  tff(c_843, plain, (![A_189, B_190]: (k1_relset_1(A_189, B_190, k2_zfmisc_1(A_189, B_190))=k1_relat_1(k2_zfmisc_1(A_189, B_190)))), inference(resolution, [status(thm)], [c_6, c_816])).
% 19.24/10.93  tff(c_3978, plain, (![B_421, A_422, C_423]: (k1_xboole_0=B_421 | k1_relset_1(A_422, B_421, C_423)=A_422 | ~v1_funct_2(C_423, A_422, B_421) | ~m1_subset_1(C_423, k1_zfmisc_1(k2_zfmisc_1(A_422, B_421))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 19.24/10.93  tff(c_4395, plain, (![B_469, A_470, A_471]: (k1_xboole_0=B_469 | k1_relset_1(A_470, B_469, A_471)=A_470 | ~v1_funct_2(A_471, A_470, B_469) | ~r1_tarski(A_471, k2_zfmisc_1(A_470, B_469)))), inference(resolution, [status(thm)], [c_18, c_3978])).
% 19.24/10.93  tff(c_4415, plain, (![B_469, A_470]: (k1_xboole_0=B_469 | k1_relset_1(A_470, B_469, k2_zfmisc_1(A_470, B_469))=A_470 | ~v1_funct_2(k2_zfmisc_1(A_470, B_469), A_470, B_469))), inference(resolution, [status(thm)], [c_6, c_4395])).
% 19.24/10.93  tff(c_4421, plain, (![B_472, A_473]: (k1_xboole_0=B_472 | k1_relat_1(k2_zfmisc_1(A_473, B_472))=A_473 | ~v1_funct_2(k2_zfmisc_1(A_473, B_472), A_473, B_472))), inference(demodulation, [status(thm), theory('equality')], [c_843, c_4415])).
% 19.24/10.93  tff(c_4442, plain, (u1_struct_0('#skF_2')=k1_xboole_0 | k1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))=u1_struct_0('#skF_1') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3776, c_4421])).
% 19.24/10.93  tff(c_4466, plain, (u1_struct_0('#skF_2')=k1_xboole_0 | u1_struct_0('#skF_1')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_3776, c_4442])).
% 19.24/10.93  tff(c_4473, plain, (u1_struct_0('#skF_1')=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_4466])).
% 19.24/10.93  tff(c_4489, plain, (~v1_partfun1('#skF_4', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4473, c_689])).
% 19.24/10.93  tff(c_4492, plain, (v4_relat_1('#skF_4', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4473, c_404])).
% 19.24/10.93  tff(c_4564, plain, (v1_partfun1('#skF_4', k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_4492, c_52])).
% 19.24/10.93  tff(c_4571, plain, (v1_partfun1('#skF_4', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_216, c_4564])).
% 19.24/10.93  tff(c_4601, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4489, c_4571])).
% 19.24/10.93  tff(c_4602, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_4466])).
% 19.24/10.93  tff(c_4667, plain, (k2_zfmisc_1(u1_struct_0('#skF_1'), k1_xboole_0)='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4602, c_3776])).
% 19.24/10.93  tff(c_4801, plain, (k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_4667, c_10])).
% 19.24/10.93  tff(c_4819, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4034, c_4801])).
% 19.24/10.93  tff(c_4821, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_3819])).
% 19.24/10.93  tff(c_533, plain, (![B_146]: (v1_partfun1(B_146, k1_relat_1(B_146)) | ~v4_relat_1(B_146, k1_relat_1(B_146)) | ~v1_relat_1(B_146))), inference(cnfTransformation, [status(thm)], [f_111])).
% 19.24/10.93  tff(c_544, plain, (v1_partfun1(k1_xboole_0, k1_relat_1(k1_xboole_0)) | ~v4_relat_1(k1_xboole_0, k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_24, c_533])).
% 19.24/10.93  tff(c_550, plain, (v1_partfun1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_219, c_407, c_24, c_544])).
% 19.24/10.93  tff(c_4840, plain, (v1_partfun1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4821, c_4821, c_550])).
% 19.24/10.93  tff(c_4820, plain, (u1_struct_0('#skF_1')=k1_xboole_0 | u1_struct_0('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_3819])).
% 19.24/10.93  tff(c_6658, plain, (u1_struct_0('#skF_1')='#skF_4' | u1_struct_0('#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4821, c_4821, c_4820])).
% 19.24/10.93  tff(c_6659, plain, (u1_struct_0('#skF_2')='#skF_4'), inference(splitLeft, [status(thm)], [c_6658])).
% 19.24/10.93  tff(c_6666, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6659, c_103])).
% 19.24/10.93  tff(c_6665, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_6659, c_489])).
% 19.24/10.93  tff(c_12, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 19.24/10.93  tff(c_4857, plain, (![B_4]: (k2_zfmisc_1('#skF_4', B_4)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4821, c_4821, c_12])).
% 19.24/10.93  tff(c_94, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_217])).
% 19.24/10.93  tff(c_92, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_217])).
% 19.24/10.93  tff(c_5256, plain, (u1_struct_0('#skF_1')='#skF_4' | u1_struct_0('#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4821, c_4821, c_4820])).
% 19.24/10.93  tff(c_5257, plain, (u1_struct_0('#skF_2')='#skF_4'), inference(splitLeft, [status(thm)], [c_5256])).
% 19.24/10.93  tff(c_5263, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5257, c_103])).
% 19.24/10.93  tff(c_4856, plain, (![A_5]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_4821, c_14])).
% 19.24/10.93  tff(c_78, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_217])).
% 19.24/10.93  tff(c_5264, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_5257, c_78])).
% 19.24/10.93  tff(c_747, plain, (![A_176, B_177]: (k1_relset_1(A_176, B_177, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_733])).
% 19.24/10.93  tff(c_758, plain, (![A_176, B_177]: (k1_relset_1(A_176, B_177, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_747])).
% 19.24/10.93  tff(c_3992, plain, (![B_421, A_422]: (k1_xboole_0=B_421 | k1_relset_1(A_422, B_421, k1_xboole_0)=A_422 | ~v1_funct_2(k1_xboole_0, A_422, B_421))), inference(resolution, [status(thm)], [c_14, c_3978])).
% 19.24/10.93  tff(c_4001, plain, (![B_421, A_422]: (k1_xboole_0=B_421 | k1_xboole_0=A_422 | ~v1_funct_2(k1_xboole_0, A_422, B_421))), inference(demodulation, [status(thm), theory('equality')], [c_758, c_3992])).
% 19.24/10.93  tff(c_5475, plain, (![B_527, A_528]: (B_527='#skF_4' | A_528='#skF_4' | ~v1_funct_2('#skF_4', A_528, B_527))), inference(demodulation, [status(thm), theory('equality')], [c_4821, c_4821, c_4821, c_4001])).
% 19.24/10.93  tff(c_5494, plain, (u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))='#skF_4' | u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))='#skF_4'), inference(resolution, [status(thm)], [c_5264, c_5475])).
% 19.24/10.93  tff(c_5510, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))='#skF_4'), inference(splitLeft, [status(thm)], [c_5494])).
% 19.24/10.93  tff(c_4859, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4821, c_4821, c_24])).
% 19.24/10.93  tff(c_76, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))))), inference(cnfTransformation, [status(thm)], [f_217])).
% 19.24/10.93  tff(c_405, plain, (v4_relat_1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(resolution, [status(thm)], [c_76, c_383])).
% 19.24/10.93  tff(c_656, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_405, c_647])).
% 19.24/10.93  tff(c_669, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_216, c_656])).
% 19.24/10.93  tff(c_5221, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))='#skF_4' | ~v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_4859, c_669])).
% 19.24/10.93  tff(c_5222, plain, (~v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(splitLeft, [status(thm)], [c_5221])).
% 19.24/10.93  tff(c_5511, plain, (~v1_partfun1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5510, c_5222])).
% 19.24/10.93  tff(c_5515, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4840, c_5511])).
% 19.24/10.93  tff(c_5516, plain, (u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))='#skF_4'), inference(splitRight, [status(thm)], [c_5494])).
% 19.24/10.93  tff(c_5518, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5516, c_5264])).
% 19.24/10.93  tff(c_5262, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_5257, c_489])).
% 19.24/10.93  tff(c_5293, plain, (v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5257, c_62])).
% 19.24/10.93  tff(c_5325, plain, (v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_5293])).
% 19.24/10.93  tff(c_5302, plain, (l1_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5257, c_473])).
% 19.24/10.93  tff(c_5331, plain, (l1_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_5302])).
% 19.24/10.93  tff(c_4858, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4821, c_4821, c_10])).
% 19.24/10.93  tff(c_1020, plain, (![B_224, A_225, C_226]: (k1_xboole_0=B_224 | k1_relset_1(A_225, B_224, C_226)=A_225 | ~v1_funct_2(C_226, A_225, B_224) | ~m1_subset_1(C_226, k1_zfmisc_1(k2_zfmisc_1(A_225, B_224))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 19.24/10.93  tff(c_1023, plain, (u1_struct_0('#skF_2')=k1_xboole_0 | k1_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4')=u1_struct_0('#skF_1') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_107, c_1020])).
% 19.24/10.93  tff(c_1043, plain, (u1_struct_0('#skF_2')=k1_xboole_0 | u1_struct_0('#skF_1')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_754, c_1023])).
% 19.24/10.93  tff(c_1051, plain, (u1_struct_0('#skF_1')=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_1043])).
% 19.24/10.93  tff(c_1061, plain, (v4_relat_1('#skF_4', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1051, c_404])).
% 19.24/10.93  tff(c_1117, plain, (v1_partfun1('#skF_4', k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1061, c_52])).
% 19.24/10.93  tff(c_1124, plain, (v1_partfun1('#skF_4', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_216, c_1117])).
% 19.24/10.93  tff(c_1057, plain, (~v1_partfun1('#skF_4', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1051, c_689])).
% 19.24/10.93  tff(c_1133, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1124, c_1057])).
% 19.24/10.93  tff(c_1134, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1043])).
% 19.24/10.93  tff(c_904, plain, (~r1_tarski(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')), '#skF_4')), inference(splitLeft, [status(thm)], [c_196])).
% 19.24/10.93  tff(c_1137, plain, (~r1_tarski(k2_zfmisc_1(u1_struct_0('#skF_1'), k1_xboole_0), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1134, c_904])).
% 19.24/10.93  tff(c_1153, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_161, c_10, c_1137])).
% 19.24/10.93  tff(c_1154, plain, (k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))='#skF_4'), inference(splitRight, [status(thm)], [c_196])).
% 19.24/10.93  tff(c_1197, plain, (u1_struct_0('#skF_2')=k1_xboole_0 | u1_struct_0('#skF_1')=k1_xboole_0 | k1_xboole_0!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1154, c_8])).
% 19.24/10.93  tff(c_1718, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_1197])).
% 19.24/10.93  tff(c_755, plain, (k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_733])).
% 19.24/10.93  tff(c_1449, plain, (![B_246, A_247, C_248]: (k1_xboole_0=B_246 | k1_relset_1(A_247, B_246, C_248)=A_247 | ~v1_funct_2(C_248, A_247, B_246) | ~m1_subset_1(C_248, k1_zfmisc_1(k2_zfmisc_1(A_247, B_246))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 19.24/10.93  tff(c_1455, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0 | k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')=u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(resolution, [status(thm)], [c_76, c_1449])).
% 19.24/10.93  tff(c_1472, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0 | u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_755, c_1455])).
% 19.24/10.93  tff(c_1531, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_1472])).
% 19.24/10.93  tff(c_1536, plain, (v4_relat_1('#skF_4', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1531, c_405])).
% 19.24/10.93  tff(c_1571, plain, (v1_partfun1('#skF_4', k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1536, c_52])).
% 19.24/10.93  tff(c_1578, plain, (v1_partfun1('#skF_4', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_216, c_1571])).
% 19.24/10.93  tff(c_1349, plain, (~v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(splitLeft, [status(thm)], [c_669])).
% 19.24/10.93  tff(c_1532, plain, (~v1_partfun1('#skF_4', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1531, c_1349])).
% 19.24/10.93  tff(c_1587, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1578, c_1532])).
% 19.24/10.93  tff(c_1588, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0), inference(splitRight, [status(thm)], [c_1472])).
% 19.24/10.93  tff(c_176, plain, (r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))))), inference(resolution, [status(thm)], [c_76, c_16])).
% 19.24/10.93  tff(c_246, plain, (k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))='#skF_4' | ~r1_tarski(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), '#skF_4')), inference(resolution, [status(thm)], [c_176, c_2])).
% 19.24/10.93  tff(c_901, plain, (~r1_tarski(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), '#skF_4')), inference(splitLeft, [status(thm)], [c_246])).
% 19.24/10.93  tff(c_1590, plain, (~r1_tarski(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), k1_xboole_0), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1588, c_901])).
% 19.24/10.93  tff(c_1599, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_161, c_10, c_1590])).
% 19.24/10.93  tff(c_1600, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_669])).
% 19.24/10.93  tff(c_1601, plain, (v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(splitRight, [status(thm)], [c_669])).
% 19.24/10.93  tff(c_1663, plain, (v1_partfun1('#skF_4', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1600, c_1601])).
% 19.24/10.93  tff(c_1602, plain, (![B_255, A_256, C_257]: (k1_xboole_0=B_255 | k1_relset_1(A_256, B_255, C_257)=A_256 | ~v1_funct_2(C_257, A_256, B_255) | ~m1_subset_1(C_257, k1_zfmisc_1(k2_zfmisc_1(A_256, B_255))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 19.24/10.93  tff(c_2107, plain, (![B_291, A_292, A_293]: (k1_xboole_0=B_291 | k1_relset_1(A_292, B_291, A_293)=A_292 | ~v1_funct_2(A_293, A_292, B_291) | ~r1_tarski(A_293, k2_zfmisc_1(A_292, B_291)))), inference(resolution, [status(thm)], [c_18, c_1602])).
% 19.24/10.93  tff(c_2127, plain, (![B_291, A_292]: (k1_xboole_0=B_291 | k1_relset_1(A_292, B_291, k2_zfmisc_1(A_292, B_291))=A_292 | ~v1_funct_2(k2_zfmisc_1(A_292, B_291), A_292, B_291))), inference(resolution, [status(thm)], [c_6, c_2107])).
% 19.24/10.93  tff(c_2136, plain, (![B_294, A_295]: (k1_xboole_0=B_294 | k1_relat_1(k2_zfmisc_1(A_295, B_294))=A_295 | ~v1_funct_2(k2_zfmisc_1(A_295, B_294), A_295, B_294))), inference(demodulation, [status(thm), theory('equality')], [c_843, c_2127])).
% 19.24/10.93  tff(c_2154, plain, (u1_struct_0('#skF_2')=k1_xboole_0 | k1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))=u1_struct_0('#skF_1') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1154, c_2136])).
% 19.24/10.93  tff(c_2176, plain, (u1_struct_0('#skF_2')=k1_xboole_0 | u1_struct_0('#skF_1')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_1154, c_2154])).
% 19.24/10.93  tff(c_2183, plain, (u1_struct_0('#skF_1')=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_2176])).
% 19.24/10.93  tff(c_2220, plain, (~v1_partfun1('#skF_4', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2183, c_689])).
% 19.24/10.93  tff(c_2226, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1663, c_2220])).
% 19.24/10.93  tff(c_2227, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_2176])).
% 19.24/10.93  tff(c_2240, plain, (k2_zfmisc_1(u1_struct_0('#skF_1'), k1_xboole_0)='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2227, c_1154])).
% 19.24/10.93  tff(c_2387, plain, (k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_2240, c_10])).
% 19.24/10.93  tff(c_2406, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1718, c_2387])).
% 19.24/10.93  tff(c_2408, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1197])).
% 19.24/10.93  tff(c_2446, plain, (![B_4]: (k2_zfmisc_1('#skF_4', B_4)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2408, c_2408, c_12])).
% 19.24/10.93  tff(c_2448, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2408, c_2408, c_24])).
% 19.24/10.93  tff(c_1664, plain, (~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1600, c_901])).
% 19.24/10.93  tff(c_3374, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_2446, c_2448, c_1664])).
% 19.24/10.93  tff(c_3375, plain, (k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))='#skF_4'), inference(splitRight, [status(thm)], [c_246])).
% 19.24/10.93  tff(c_5230, plain, (![D_500, A_501, B_502]: (v5_pre_topc(D_500, A_501, B_502) | ~v5_pre_topc(D_500, g1_pre_topc(u1_struct_0(A_501), u1_pre_topc(A_501)), B_502) | ~m1_subset_1(D_500, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_501), u1_pre_topc(A_501))), u1_struct_0(B_502)))) | ~v1_funct_2(D_500, u1_struct_0(g1_pre_topc(u1_struct_0(A_501), u1_pre_topc(A_501))), u1_struct_0(B_502)) | ~m1_subset_1(D_500, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_501), u1_struct_0(B_502)))) | ~v1_funct_2(D_500, u1_struct_0(A_501), u1_struct_0(B_502)) | ~v1_funct_1(D_500) | ~l1_pre_topc(B_502) | ~v2_pre_topc(B_502) | ~l1_pre_topc(A_501) | ~v2_pre_topc(A_501))), inference(cnfTransformation, [status(thm)], [f_158])).
% 19.24/10.93  tff(c_5237, plain, (![D_500]: (v5_pre_topc(D_500, '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc(D_500, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_subset_1(D_500, k1_zfmisc_1('#skF_4')) | ~v1_funct_2(D_500, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1(D_500, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))))) | ~v1_funct_2(D_500, u1_struct_0('#skF_1'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~v1_funct_1(D_500) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_3375, c_5230])).
% 19.24/10.93  tff(c_5246, plain, (![D_500]: (v5_pre_topc(D_500, '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc(D_500, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_subset_1(D_500, k1_zfmisc_1('#skF_4')) | ~v1_funct_2(D_500, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1(D_500, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))))) | ~v1_funct_2(D_500, u1_struct_0('#skF_1'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~v1_funct_1(D_500) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_5237])).
% 19.24/10.93  tff(c_6585, plain, (![D_618]: (v5_pre_topc(D_618, '#skF_1', g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc(D_618, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v1_funct_2(D_618, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4') | ~m1_subset_1(D_618, k1_zfmisc_1('#skF_4')) | ~v1_funct_2(D_618, u1_struct_0('#skF_1'), '#skF_4') | ~v1_funct_1(D_618))), inference(demodulation, [status(thm), theory('equality')], [c_5325, c_5257, c_5331, c_5257, c_5516, c_5257, c_4858, c_5516, c_5257, c_5516, c_5257, c_5257, c_5257, c_5246])).
% 19.24/10.93  tff(c_6592, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4')) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_5262, c_6585])).
% 19.24/10.93  tff(c_6598, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_5263, c_4856, c_5518, c_6592])).
% 19.24/10.93  tff(c_5335, plain, (![D_504, A_505, B_506]: (v5_pre_topc(D_504, A_505, B_506) | ~v5_pre_topc(D_504, A_505, g1_pre_topc(u1_struct_0(B_506), u1_pre_topc(B_506))) | ~m1_subset_1(D_504, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_505), u1_struct_0(g1_pre_topc(u1_struct_0(B_506), u1_pre_topc(B_506)))))) | ~v1_funct_2(D_504, u1_struct_0(A_505), u1_struct_0(g1_pre_topc(u1_struct_0(B_506), u1_pre_topc(B_506)))) | ~m1_subset_1(D_504, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_505), u1_struct_0(B_506)))) | ~v1_funct_2(D_504, u1_struct_0(A_505), u1_struct_0(B_506)) | ~v1_funct_1(D_504) | ~l1_pre_topc(B_506) | ~v2_pre_topc(B_506) | ~l1_pre_topc(A_505) | ~v2_pre_topc(A_505))), inference(cnfTransformation, [status(thm)], [f_187])).
% 19.24/10.93  tff(c_5910, plain, (![A_564, A_565, B_566]: (v5_pre_topc(A_564, A_565, B_566) | ~v5_pre_topc(A_564, A_565, g1_pre_topc(u1_struct_0(B_566), u1_pre_topc(B_566))) | ~v1_funct_2(A_564, u1_struct_0(A_565), u1_struct_0(g1_pre_topc(u1_struct_0(B_566), u1_pre_topc(B_566)))) | ~m1_subset_1(A_564, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_565), u1_struct_0(B_566)))) | ~v1_funct_2(A_564, u1_struct_0(A_565), u1_struct_0(B_566)) | ~v1_funct_1(A_564) | ~l1_pre_topc(B_566) | ~v2_pre_topc(B_566) | ~l1_pre_topc(A_565) | ~v2_pre_topc(A_565) | ~r1_tarski(A_564, k2_zfmisc_1(u1_struct_0(A_565), u1_struct_0(g1_pre_topc(u1_struct_0(B_566), u1_pre_topc(B_566))))))), inference(resolution, [status(thm)], [c_18, c_5335])).
% 19.24/10.93  tff(c_6456, plain, (![A_613, B_614]: (v5_pre_topc(k2_zfmisc_1(u1_struct_0(A_613), u1_struct_0(g1_pre_topc(u1_struct_0(B_614), u1_pre_topc(B_614)))), A_613, B_614) | ~v5_pre_topc(k2_zfmisc_1(u1_struct_0(A_613), u1_struct_0(g1_pre_topc(u1_struct_0(B_614), u1_pre_topc(B_614)))), A_613, g1_pre_topc(u1_struct_0(B_614), u1_pre_topc(B_614))) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(A_613), u1_struct_0(g1_pre_topc(u1_struct_0(B_614), u1_pre_topc(B_614)))), u1_struct_0(A_613), u1_struct_0(g1_pre_topc(u1_struct_0(B_614), u1_pre_topc(B_614)))) | ~m1_subset_1(k2_zfmisc_1(u1_struct_0(A_613), u1_struct_0(g1_pre_topc(u1_struct_0(B_614), u1_pre_topc(B_614)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_613), u1_struct_0(B_614)))) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(A_613), u1_struct_0(g1_pre_topc(u1_struct_0(B_614), u1_pre_topc(B_614)))), u1_struct_0(A_613), u1_struct_0(B_614)) | ~v1_funct_1(k2_zfmisc_1(u1_struct_0(A_613), u1_struct_0(g1_pre_topc(u1_struct_0(B_614), u1_pre_topc(B_614))))) | ~l1_pre_topc(B_614) | ~v2_pre_topc(B_614) | ~l1_pre_topc(A_613) | ~v2_pre_topc(A_613))), inference(resolution, [status(thm)], [c_6, c_5910])).
% 19.24/10.93  tff(c_6480, plain, (![A_613]: (v5_pre_topc(k2_zfmisc_1(u1_struct_0(A_613), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), A_613, '#skF_2') | ~v5_pre_topc(k2_zfmisc_1(u1_struct_0(A_613), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), A_613, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(A_613), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), u1_struct_0(A_613), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1(k2_zfmisc_1(u1_struct_0(A_613), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_613), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(A_613), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), u1_struct_0(A_613), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_zfmisc_1(u1_struct_0(A_613), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(A_613) | ~v2_pre_topc(A_613))), inference(superposition, [status(thm), theory('equality')], [c_5257, c_6456])).
% 19.24/10.93  tff(c_6500, plain, (![A_613]: (v5_pre_topc('#skF_4', A_613, '#skF_2') | ~v5_pre_topc('#skF_4', A_613, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_613), '#skF_4') | ~l1_pre_topc(A_613) | ~v2_pre_topc(A_613))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_80, c_4858, c_5516, c_5257, c_4858, c_5516, c_5257, c_5257, c_4856, c_4858, c_5516, c_4858, c_5257, c_5257, c_5516, c_4858, c_5516, c_5257, c_4858, c_5516, c_5257, c_5257, c_4858, c_5516, c_5257, c_6480])).
% 19.24/10.93  tff(c_6601, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_6598, c_6500])).
% 19.24/10.93  tff(c_6604, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_5263, c_6601])).
% 19.24/10.93  tff(c_6606, plain, $false, inference(negUnitSimplification, [status(thm)], [c_551, c_6604])).
% 19.24/10.93  tff(c_6607, plain, (u1_struct_0('#skF_1')='#skF_4'), inference(splitRight, [status(thm)], [c_5256])).
% 19.24/10.93  tff(c_6614, plain, (~v1_partfun1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6607, c_689])).
% 19.24/10.93  tff(c_6621, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4840, c_6614])).
% 19.24/10.93  tff(c_6622, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))='#skF_4'), inference(splitRight, [status(thm)], [c_5221])).
% 19.24/10.93  tff(c_6914, plain, (l1_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_6622, c_473])).
% 19.24/10.93  tff(c_7531, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_6914])).
% 19.24/10.93  tff(c_7534, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_473, c_7531])).
% 19.24/10.93  tff(c_7538, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_7534])).
% 19.24/10.93  tff(c_7540, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_6914])).
% 19.24/10.93  tff(c_6905, plain, (v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_6622, c_62])).
% 19.24/10.93  tff(c_7906, plain, (v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_7540, c_6905])).
% 19.24/10.93  tff(c_7907, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_7906])).
% 19.24/10.93  tff(c_7910, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_7907])).
% 19.24/10.93  tff(c_7914, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_7910])).
% 19.24/10.93  tff(c_7916, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_7906])).
% 19.24/10.93  tff(c_44, plain, (![C_28, B_27]: (v1_funct_2(C_28, k1_xboole_0, B_27) | k1_relset_1(k1_xboole_0, B_27, C_28)!=k1_xboole_0 | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_27))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 19.24/10.93  tff(c_861, plain, (![C_194, B_195]: (v1_funct_2(C_194, k1_xboole_0, B_195) | k1_relset_1(k1_xboole_0, B_195, C_194)!=k1_xboole_0 | ~m1_subset_1(C_194, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_44])).
% 19.24/10.93  tff(c_867, plain, (![B_195]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_195) | k1_relset_1(k1_xboole_0, B_195, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_861])).
% 19.24/10.93  tff(c_871, plain, (![B_195]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_195))), inference(demodulation, [status(thm), theory('equality')], [c_758, c_867])).
% 19.24/10.93  tff(c_4827, plain, (![B_195]: (v1_funct_2('#skF_4', '#skF_4', B_195))), inference(demodulation, [status(thm), theory('equality')], [c_4821, c_4821, c_871])).
% 19.24/10.93  tff(c_3844, plain, (![C_412, A_413, B_414]: (v1_funct_2(C_412, A_413, B_414) | ~v1_partfun1(C_412, A_413) | ~v1_funct_1(C_412) | ~m1_subset_1(C_412, k1_zfmisc_1(k2_zfmisc_1(A_413, B_414))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 19.24/10.93  tff(c_6939, plain, (![A_645, A_646, B_647]: (v1_funct_2(A_645, A_646, B_647) | ~v1_partfun1(A_645, A_646) | ~v1_funct_1(A_645) | ~r1_tarski(A_645, k2_zfmisc_1(A_646, B_647)))), inference(resolution, [status(thm)], [c_18, c_3844])).
% 19.24/10.93  tff(c_6957, plain, (![A_646, B_647]: (v1_funct_2(k2_zfmisc_1(A_646, B_647), A_646, B_647) | ~v1_partfun1(k2_zfmisc_1(A_646, B_647), A_646) | ~v1_funct_1(k2_zfmisc_1(A_646, B_647)))), inference(resolution, [status(thm)], [c_6, c_6939])).
% 19.24/10.93  tff(c_6738, plain, (![D_625, A_626, B_627]: (v5_pre_topc(D_625, A_626, B_627) | ~v5_pre_topc(D_625, A_626, g1_pre_topc(u1_struct_0(B_627), u1_pre_topc(B_627))) | ~m1_subset_1(D_625, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_626), u1_struct_0(g1_pre_topc(u1_struct_0(B_627), u1_pre_topc(B_627)))))) | ~v1_funct_2(D_625, u1_struct_0(A_626), u1_struct_0(g1_pre_topc(u1_struct_0(B_627), u1_pre_topc(B_627)))) | ~m1_subset_1(D_625, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_626), u1_struct_0(B_627)))) | ~v1_funct_2(D_625, u1_struct_0(A_626), u1_struct_0(B_627)) | ~v1_funct_1(D_625) | ~l1_pre_topc(B_627) | ~v2_pre_topc(B_627) | ~l1_pre_topc(A_626) | ~v2_pre_topc(A_626))), inference(cnfTransformation, [status(thm)], [f_187])).
% 19.24/10.93  tff(c_7121, plain, (![A_670, A_671, B_672]: (v5_pre_topc(A_670, A_671, B_672) | ~v5_pre_topc(A_670, A_671, g1_pre_topc(u1_struct_0(B_672), u1_pre_topc(B_672))) | ~v1_funct_2(A_670, u1_struct_0(A_671), u1_struct_0(g1_pre_topc(u1_struct_0(B_672), u1_pre_topc(B_672)))) | ~m1_subset_1(A_670, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_671), u1_struct_0(B_672)))) | ~v1_funct_2(A_670, u1_struct_0(A_671), u1_struct_0(B_672)) | ~v1_funct_1(A_670) | ~l1_pre_topc(B_672) | ~v2_pre_topc(B_672) | ~l1_pre_topc(A_671) | ~v2_pre_topc(A_671) | ~r1_tarski(A_670, k2_zfmisc_1(u1_struct_0(A_671), u1_struct_0(g1_pre_topc(u1_struct_0(B_672), u1_pre_topc(B_672))))))), inference(resolution, [status(thm)], [c_18, c_6738])).
% 19.24/10.93  tff(c_7478, plain, (![A_706, B_707]: (v5_pre_topc(k2_zfmisc_1(u1_struct_0(A_706), u1_struct_0(g1_pre_topc(u1_struct_0(B_707), u1_pre_topc(B_707)))), A_706, B_707) | ~v5_pre_topc(k2_zfmisc_1(u1_struct_0(A_706), u1_struct_0(g1_pre_topc(u1_struct_0(B_707), u1_pre_topc(B_707)))), A_706, g1_pre_topc(u1_struct_0(B_707), u1_pre_topc(B_707))) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(A_706), u1_struct_0(g1_pre_topc(u1_struct_0(B_707), u1_pre_topc(B_707)))), u1_struct_0(A_706), u1_struct_0(g1_pre_topc(u1_struct_0(B_707), u1_pre_topc(B_707)))) | ~m1_subset_1(k2_zfmisc_1(u1_struct_0(A_706), u1_struct_0(g1_pre_topc(u1_struct_0(B_707), u1_pre_topc(B_707)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_706), u1_struct_0(B_707)))) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(A_706), u1_struct_0(g1_pre_topc(u1_struct_0(B_707), u1_pre_topc(B_707)))), u1_struct_0(A_706), u1_struct_0(B_707)) | ~v1_funct_1(k2_zfmisc_1(u1_struct_0(A_706), u1_struct_0(g1_pre_topc(u1_struct_0(B_707), u1_pre_topc(B_707))))) | ~l1_pre_topc(B_707) | ~v2_pre_topc(B_707) | ~l1_pre_topc(A_706) | ~v2_pre_topc(A_706))), inference(resolution, [status(thm)], [c_6, c_7121])).
% 19.24/10.93  tff(c_8155, plain, (![A_742, B_743]: (v5_pre_topc(k2_zfmisc_1(u1_struct_0(A_742), u1_struct_0(g1_pre_topc(u1_struct_0(B_743), u1_pre_topc(B_743)))), A_742, B_743) | ~v5_pre_topc(k2_zfmisc_1(u1_struct_0(A_742), u1_struct_0(g1_pre_topc(u1_struct_0(B_743), u1_pre_topc(B_743)))), A_742, g1_pre_topc(u1_struct_0(B_743), u1_pre_topc(B_743))) | ~m1_subset_1(k2_zfmisc_1(u1_struct_0(A_742), u1_struct_0(g1_pre_topc(u1_struct_0(B_743), u1_pre_topc(B_743)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_742), u1_struct_0(B_743)))) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(A_742), u1_struct_0(g1_pre_topc(u1_struct_0(B_743), u1_pre_topc(B_743)))), u1_struct_0(A_742), u1_struct_0(B_743)) | ~l1_pre_topc(B_743) | ~v2_pre_topc(B_743) | ~l1_pre_topc(A_742) | ~v2_pre_topc(A_742) | ~v1_partfun1(k2_zfmisc_1(u1_struct_0(A_742), u1_struct_0(g1_pre_topc(u1_struct_0(B_743), u1_pre_topc(B_743)))), u1_struct_0(A_742)) | ~v1_funct_1(k2_zfmisc_1(u1_struct_0(A_742), u1_struct_0(g1_pre_topc(u1_struct_0(B_743), u1_pre_topc(B_743))))))), inference(resolution, [status(thm)], [c_6957, c_7478])).
% 19.24/10.93  tff(c_8157, plain, (![B_743]: (v5_pre_topc(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0(B_743), u1_pre_topc(B_743)))), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_743) | ~v5_pre_topc(k2_zfmisc_1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(B_743), u1_pre_topc(B_743)))), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0(B_743), u1_pre_topc(B_743))) | ~m1_subset_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0(B_743), u1_pre_topc(B_743)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_743)))) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0(B_743), u1_pre_topc(B_743)))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_743)) | ~l1_pre_topc(B_743) | ~v2_pre_topc(B_743) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v1_partfun1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0(B_743), u1_pre_topc(B_743)))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))) | ~v1_funct_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0(B_743), u1_pre_topc(B_743))))))), inference(superposition, [status(thm), theory('equality')], [c_6622, c_8155])).
% 19.24/10.93  tff(c_8184, plain, (![B_744]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_744) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0(B_744), u1_pre_topc(B_744))) | ~l1_pre_topc(B_744) | ~v2_pre_topc(B_744))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_4857, c_6622, c_4840, c_4857, c_6622, c_6622, c_7916, c_7540, c_4827, c_4857, c_6622, c_6622, c_4856, c_4857, c_6622, c_6622, c_4857, c_4857, c_6622, c_8157])).
% 19.24/10.93  tff(c_8204, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6659, c_8184])).
% 19.24/10.93  tff(c_8218, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_6665, c_8204])).
% 19.24/10.93  tff(c_6638, plain, (![D_621, A_622, B_623]: (v5_pre_topc(D_621, A_622, B_623) | ~v5_pre_topc(D_621, g1_pre_topc(u1_struct_0(A_622), u1_pre_topc(A_622)), B_623) | ~m1_subset_1(D_621, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_622), u1_pre_topc(A_622))), u1_struct_0(B_623)))) | ~v1_funct_2(D_621, u1_struct_0(g1_pre_topc(u1_struct_0(A_622), u1_pre_topc(A_622))), u1_struct_0(B_623)) | ~m1_subset_1(D_621, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_622), u1_struct_0(B_623)))) | ~v1_funct_2(D_621, u1_struct_0(A_622), u1_struct_0(B_623)) | ~v1_funct_1(D_621) | ~l1_pre_topc(B_623) | ~v2_pre_topc(B_623) | ~l1_pre_topc(A_622) | ~v2_pre_topc(A_622))), inference(cnfTransformation, [status(thm)], [f_158])).
% 19.24/10.93  tff(c_7051, plain, (![A_661, A_662, B_663]: (v5_pre_topc(A_661, A_662, B_663) | ~v5_pre_topc(A_661, g1_pre_topc(u1_struct_0(A_662), u1_pre_topc(A_662)), B_663) | ~v1_funct_2(A_661, u1_struct_0(g1_pre_topc(u1_struct_0(A_662), u1_pre_topc(A_662))), u1_struct_0(B_663)) | ~m1_subset_1(A_661, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_662), u1_struct_0(B_663)))) | ~v1_funct_2(A_661, u1_struct_0(A_662), u1_struct_0(B_663)) | ~v1_funct_1(A_661) | ~l1_pre_topc(B_663) | ~v2_pre_topc(B_663) | ~l1_pre_topc(A_662) | ~v2_pre_topc(A_662) | ~r1_tarski(A_661, k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_662), u1_pre_topc(A_662))), u1_struct_0(B_663))))), inference(resolution, [status(thm)], [c_18, c_6638])).
% 19.24/10.93  tff(c_7570, plain, (![A_710, B_711]: (v5_pre_topc(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_710), u1_pre_topc(A_710))), u1_struct_0(B_711)), A_710, B_711) | ~v5_pre_topc(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_710), u1_pre_topc(A_710))), u1_struct_0(B_711)), g1_pre_topc(u1_struct_0(A_710), u1_pre_topc(A_710)), B_711) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_710), u1_pre_topc(A_710))), u1_struct_0(B_711)), u1_struct_0(g1_pre_topc(u1_struct_0(A_710), u1_pre_topc(A_710))), u1_struct_0(B_711)) | ~m1_subset_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_710), u1_pre_topc(A_710))), u1_struct_0(B_711)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_710), u1_struct_0(B_711)))) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_710), u1_pre_topc(A_710))), u1_struct_0(B_711)), u1_struct_0(A_710), u1_struct_0(B_711)) | ~v1_funct_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_710), u1_pre_topc(A_710))), u1_struct_0(B_711))) | ~l1_pre_topc(B_711) | ~v2_pre_topc(B_711) | ~l1_pre_topc(A_710) | ~v2_pre_topc(A_710))), inference(resolution, [status(thm)], [c_6, c_7051])).
% 19.24/10.93  tff(c_7588, plain, (![B_711]: (v5_pre_topc(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_711)), '#skF_1', B_711) | ~v5_pre_topc(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_711)), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_711) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_711)), '#skF_4', u1_struct_0(B_711)) | ~m1_subset_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_711)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_711)))) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_711)), u1_struct_0('#skF_1'), u1_struct_0(B_711)) | ~v1_funct_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_711))) | ~l1_pre_topc(B_711) | ~v2_pre_topc(B_711) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_6622, c_7570])).
% 19.24/10.93  tff(c_7614, plain, (![B_711]: (v5_pre_topc('#skF_4', '#skF_1', B_711) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_711) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0(B_711)) | ~l1_pre_topc(B_711) | ~v2_pre_topc(B_711))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_80, c_4857, c_6622, c_4857, c_6622, c_4856, c_4857, c_6622, c_4827, c_4857, c_6622, c_4857, c_6622, c_4857, c_6622, c_7588])).
% 19.24/10.93  tff(c_8221, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_8218, c_7614])).
% 19.24/10.93  tff(c_8224, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_6666, c_6659, c_8221])).
% 19.24/10.93  tff(c_8226, plain, $false, inference(negUnitSimplification, [status(thm)], [c_551, c_8224])).
% 19.24/10.93  tff(c_8227, plain, (u1_struct_0('#skF_1')='#skF_4'), inference(splitRight, [status(thm)], [c_6658])).
% 19.24/10.93  tff(c_8234, plain, (~v1_partfun1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8227, c_689])).
% 19.24/10.93  tff(c_8241, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4840, c_8234])).
% 19.24/10.93  tff(c_8242, plain, (u1_struct_0('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_672])).
% 19.24/10.93  tff(c_8251, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_8242, c_193])).
% 19.24/10.93  tff(c_8254, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_8242, c_103])).
% 19.24/10.93  tff(c_8255, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_8242, c_78])).
% 19.24/10.93  tff(c_8253, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))))), inference(demodulation, [status(thm), theory('equality')], [c_8242, c_76])).
% 19.24/10.93  tff(c_34, plain, (![A_20, B_21, C_22]: (k1_relset_1(A_20, B_21, C_22)=k1_relat_1(C_22) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 19.24/10.93  tff(c_8469, plain, (k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_8253, c_34])).
% 19.24/10.93  tff(c_8250, plain, (r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))))), inference(demodulation, [status(thm), theory('equality')], [c_8242, c_176])).
% 19.24/10.93  tff(c_13141, plain, (![B_1071, A_1072, C_1073]: (k1_xboole_0=B_1071 | k1_relset_1(A_1072, B_1071, C_1073)=A_1072 | ~v1_funct_2(C_1073, A_1072, B_1071) | ~m1_subset_1(C_1073, k1_zfmisc_1(k2_zfmisc_1(A_1072, B_1071))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 19.24/10.93  tff(c_13337, plain, (![B_1096, A_1097, A_1098]: (k1_xboole_0=B_1096 | k1_relset_1(A_1097, B_1096, A_1098)=A_1097 | ~v1_funct_2(A_1098, A_1097, B_1096) | ~r1_tarski(A_1098, k2_zfmisc_1(A_1097, B_1096)))), inference(resolution, [status(thm)], [c_18, c_13141])).
% 19.24/10.93  tff(c_13340, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0 | k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')=u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(resolution, [status(thm)], [c_8250, c_13337])).
% 19.24/10.93  tff(c_13360, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0 | u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8255, c_8469, c_13340])).
% 19.24/10.93  tff(c_13483, plain, (u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_13360])).
% 19.24/10.93  tff(c_8252, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_8242, c_107])).
% 19.24/10.93  tff(c_8259, plain, (v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_8242, c_62])).
% 19.24/10.93  tff(c_8275, plain, (v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_8259])).
% 19.24/10.93  tff(c_8268, plain, (l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_8242, c_473])).
% 19.24/10.93  tff(c_8281, plain, (l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_8268])).
% 19.24/10.93  tff(c_8247, plain, (v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_8242, c_489])).
% 19.24/10.93  tff(c_13251, plain, (![D_1082, A_1083, B_1084]: (v5_pre_topc(D_1082, A_1083, B_1084) | ~v5_pre_topc(D_1082, A_1083, g1_pre_topc(u1_struct_0(B_1084), u1_pre_topc(B_1084))) | ~m1_subset_1(D_1082, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1083), u1_struct_0(g1_pre_topc(u1_struct_0(B_1084), u1_pre_topc(B_1084)))))) | ~v1_funct_2(D_1082, u1_struct_0(A_1083), u1_struct_0(g1_pre_topc(u1_struct_0(B_1084), u1_pre_topc(B_1084)))) | ~m1_subset_1(D_1082, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1083), u1_struct_0(B_1084)))) | ~v1_funct_2(D_1082, u1_struct_0(A_1083), u1_struct_0(B_1084)) | ~v1_funct_1(D_1082) | ~l1_pre_topc(B_1084) | ~v2_pre_topc(B_1084) | ~l1_pre_topc(A_1083) | ~v2_pre_topc(A_1083))), inference(cnfTransformation, [status(thm)], [f_187])).
% 19.24/10.93  tff(c_13254, plain, (v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), '#skF_2') | ~v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_8253, c_13251])).
% 19.24/10.93  tff(c_13271, plain, (v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_8275, c_8281, c_90, c_88, c_80, c_8255, c_8247, c_13254])).
% 19.24/10.93  tff(c_13935, plain, (v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8254, c_13483, c_8252, c_13483, c_13271])).
% 19.24/10.93  tff(c_13454, plain, (![D_1103, A_1104, B_1105]: (v5_pre_topc(D_1103, A_1104, B_1105) | ~v5_pre_topc(D_1103, g1_pre_topc(u1_struct_0(A_1104), u1_pre_topc(A_1104)), B_1105) | ~m1_subset_1(D_1103, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1104), u1_pre_topc(A_1104))), u1_struct_0(B_1105)))) | ~v1_funct_2(D_1103, u1_struct_0(g1_pre_topc(u1_struct_0(A_1104), u1_pre_topc(A_1104))), u1_struct_0(B_1105)) | ~m1_subset_1(D_1103, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1104), u1_struct_0(B_1105)))) | ~v1_funct_2(D_1103, u1_struct_0(A_1104), u1_struct_0(B_1105)) | ~v1_funct_1(D_1103) | ~l1_pre_topc(B_1105) | ~v2_pre_topc(B_1105) | ~l1_pre_topc(A_1104) | ~v2_pre_topc(A_1104))), inference(cnfTransformation, [status(thm)], [f_158])).
% 19.24/10.93  tff(c_14303, plain, (![A_1161, A_1162, B_1163]: (v5_pre_topc(A_1161, A_1162, B_1163) | ~v5_pre_topc(A_1161, g1_pre_topc(u1_struct_0(A_1162), u1_pre_topc(A_1162)), B_1163) | ~v1_funct_2(A_1161, u1_struct_0(g1_pre_topc(u1_struct_0(A_1162), u1_pre_topc(A_1162))), u1_struct_0(B_1163)) | ~m1_subset_1(A_1161, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1162), u1_struct_0(B_1163)))) | ~v1_funct_2(A_1161, u1_struct_0(A_1162), u1_struct_0(B_1163)) | ~v1_funct_1(A_1161) | ~l1_pre_topc(B_1163) | ~v2_pre_topc(B_1163) | ~l1_pre_topc(A_1162) | ~v2_pre_topc(A_1162) | ~r1_tarski(A_1161, k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1162), u1_pre_topc(A_1162))), u1_struct_0(B_1163))))), inference(resolution, [status(thm)], [c_18, c_13454])).
% 19.24/10.93  tff(c_14312, plain, (![A_1161, B_1163]: (v5_pre_topc(A_1161, '#skF_1', B_1163) | ~v5_pre_topc(A_1161, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_1163) | ~v1_funct_2(A_1161, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_1163)) | ~m1_subset_1(A_1161, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_1163)))) | ~v1_funct_2(A_1161, u1_struct_0('#skF_1'), u1_struct_0(B_1163)) | ~v1_funct_1(A_1161) | ~l1_pre_topc(B_1163) | ~v2_pre_topc(B_1163) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(A_1161, k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(B_1163))))), inference(superposition, [status(thm), theory('equality')], [c_8242, c_14303])).
% 19.24/10.93  tff(c_14662, plain, (![A_1185, B_1186]: (v5_pre_topc(A_1185, '#skF_1', B_1186) | ~v5_pre_topc(A_1185, g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), B_1186) | ~m1_subset_1(A_1185, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_1186)))) | ~v1_funct_2(A_1185, k1_relat_1('#skF_4'), u1_struct_0(B_1186)) | ~v1_funct_1(A_1185) | ~l1_pre_topc(B_1186) | ~v2_pre_topc(B_1186) | ~r1_tarski(A_1185, k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_1186))))), inference(demodulation, [status(thm), theory('equality')], [c_13483, c_94, c_92, c_8242, c_8242, c_13483, c_8242, c_8242, c_14312])).
% 19.24/10.93  tff(c_14671, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), '#skF_2') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~r1_tarski('#skF_4', k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_8252, c_14662])).
% 19.24/10.93  tff(c_14690, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8251, c_90, c_88, c_80, c_8254, c_13935, c_14671])).
% 19.24/10.93  tff(c_14692, plain, $false, inference(negUnitSimplification, [status(thm)], [c_551, c_14690])).
% 19.24/10.93  tff(c_14693, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0), inference(splitRight, [status(thm)], [c_13360])).
% 19.24/10.93  tff(c_14697, plain, (r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_14693, c_8250])).
% 19.24/10.93  tff(c_14702, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_14697])).
% 19.24/10.93  tff(c_163, plain, (![B_86, A_87]: (B_86=A_87 | ~r1_tarski(B_86, A_87) | ~r1_tarski(A_87, B_86))), inference(cnfTransformation, [status(thm)], [f_31])).
% 19.24/10.93  tff(c_168, plain, (![A_5]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k1_xboole_0))), inference(resolution, [status(thm)], [c_161, c_163])).
% 19.24/10.93  tff(c_14782, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_14702, c_168])).
% 19.24/10.93  tff(c_14833, plain, (![B_4]: (k2_zfmisc_1('#skF_4', B_4)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14782, c_14782, c_12])).
% 19.24/10.93  tff(c_14835, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_14782, c_14782, c_24])).
% 19.24/10.93  tff(c_13249, plain, (k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'))='#skF_4' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8242, c_8242, c_196])).
% 19.24/10.93  tff(c_13250, plain, (~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2')), '#skF_4')), inference(splitLeft, [status(thm)], [c_13249])).
% 19.24/10.93  tff(c_14868, plain, (~r1_tarski(k2_zfmisc_1('#skF_4', u1_struct_0('#skF_2')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14835, c_13250])).
% 19.24/10.93  tff(c_15534, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_14833, c_14868])).
% 19.24/10.93  tff(c_15535, plain, (k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'))='#skF_4'), inference(splitRight, [status(thm)], [c_13249])).
% 19.24/10.93  tff(c_15587, plain, (u1_struct_0('#skF_2')=k1_xboole_0 | k1_relat_1('#skF_4')=k1_xboole_0 | k1_xboole_0!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_15535, c_8])).
% 19.24/10.93  tff(c_15695, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_15587])).
% 19.24/10.93  tff(c_8243, plain, (v1_partfun1('#skF_4', u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_672])).
% 19.24/10.93  tff(c_8285, plain, (v1_partfun1('#skF_4', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_8242, c_8243])).
% 19.24/10.93  tff(c_13144, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0 | k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')=u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(resolution, [status(thm)], [c_8253, c_13141])).
% 19.24/10.93  tff(c_13164, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0 | k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')=u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_8255, c_13144])).
% 19.24/10.93  tff(c_18557, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0 | u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8469, c_13164])).
% 19.24/10.93  tff(c_18558, plain, (u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_18557])).
% 19.24/10.93  tff(c_18194, plain, (u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_8242, c_8242, c_669])).
% 19.24/10.93  tff(c_18195, plain, (~v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))))), inference(splitLeft, [status(thm)], [c_18194])).
% 19.24/10.93  tff(c_18562, plain, (~v1_partfun1('#skF_4', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_18558, c_18195])).
% 19.24/10.93  tff(c_18568, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8285, c_18562])).
% 19.24/10.93  tff(c_18569, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0), inference(splitRight, [status(thm)], [c_18557])).
% 19.24/10.93  tff(c_15538, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_15535, c_8252])).
% 19.24/10.93  tff(c_15948, plain, (![B_1265, A_1266, A_1267]: (k1_xboole_0=B_1265 | k1_relset_1(A_1266, B_1265, A_1267)=A_1266 | ~v1_funct_2(A_1267, A_1266, B_1265) | ~r1_tarski(A_1267, k2_zfmisc_1(A_1266, B_1265)))), inference(resolution, [status(thm)], [c_18, c_13141])).
% 19.24/10.93  tff(c_15954, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0 | k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')=u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(resolution, [status(thm)], [c_8250, c_15948])).
% 19.24/10.93  tff(c_15971, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0 | u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8255, c_8469, c_15954])).
% 19.24/10.93  tff(c_16082, plain, (u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_15971])).
% 19.24/10.93  tff(c_15977, plain, (u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_8242, c_8242, c_669])).
% 19.24/10.93  tff(c_15978, plain, (~v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))))), inference(splitLeft, [status(thm)], [c_15977])).
% 19.24/10.93  tff(c_16112, plain, (~v1_partfun1('#skF_4', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_16082, c_15978])).
% 19.24/10.93  tff(c_16122, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8285, c_16112])).
% 19.24/10.93  tff(c_16123, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0), inference(splitRight, [status(thm)], [c_15971])).
% 19.24/10.93  tff(c_15820, plain, (k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))='#skF_4' | ~r1_tarski(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8242, c_8242, c_246])).
% 19.24/10.93  tff(c_15821, plain, (~r1_tarski(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), '#skF_4')), inference(splitLeft, [status(thm)], [c_15820])).
% 19.24/10.93  tff(c_16125, plain, (~r1_tarski(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), k1_xboole_0), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16123, c_15821])).
% 19.24/10.93  tff(c_16134, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_161, c_10, c_16125])).
% 19.24/10.93  tff(c_16135, plain, (u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_15977])).
% 19.24/10.93  tff(c_15911, plain, (![D_1261, A_1262, B_1263]: (v5_pre_topc(D_1261, A_1262, B_1263) | ~v5_pre_topc(D_1261, A_1262, g1_pre_topc(u1_struct_0(B_1263), u1_pre_topc(B_1263))) | ~m1_subset_1(D_1261, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1262), u1_struct_0(g1_pre_topc(u1_struct_0(B_1263), u1_pre_topc(B_1263)))))) | ~v1_funct_2(D_1261, u1_struct_0(A_1262), u1_struct_0(g1_pre_topc(u1_struct_0(B_1263), u1_pre_topc(B_1263)))) | ~m1_subset_1(D_1261, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1262), u1_struct_0(B_1263)))) | ~v1_funct_2(D_1261, u1_struct_0(A_1262), u1_struct_0(B_1263)) | ~v1_funct_1(D_1261) | ~l1_pre_topc(B_1263) | ~v2_pre_topc(B_1263) | ~l1_pre_topc(A_1262) | ~v2_pre_topc(A_1262))), inference(cnfTransformation, [status(thm)], [f_187])).
% 19.24/10.93  tff(c_15914, plain, (v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), '#skF_2') | ~v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_8253, c_15911])).
% 19.24/10.93  tff(c_15931, plain, (v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_8275, c_8281, c_90, c_88, c_80, c_8255, c_8247, c_15914])).
% 19.24/10.93  tff(c_17044, plain, (v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8254, c_16135, c_15538, c_15535, c_16135, c_15931])).
% 19.24/10.93  tff(c_15794, plain, (![D_1246, A_1247, B_1248]: (v5_pre_topc(D_1246, A_1247, B_1248) | ~v5_pre_topc(D_1246, g1_pre_topc(u1_struct_0(A_1247), u1_pre_topc(A_1247)), B_1248) | ~m1_subset_1(D_1246, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1247), u1_pre_topc(A_1247))), u1_struct_0(B_1248)))) | ~v1_funct_2(D_1246, u1_struct_0(g1_pre_topc(u1_struct_0(A_1247), u1_pre_topc(A_1247))), u1_struct_0(B_1248)) | ~m1_subset_1(D_1246, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1247), u1_struct_0(B_1248)))) | ~v1_funct_2(D_1246, u1_struct_0(A_1247), u1_struct_0(B_1248)) | ~v1_funct_1(D_1246) | ~l1_pre_topc(B_1248) | ~v2_pre_topc(B_1248) | ~l1_pre_topc(A_1247) | ~v2_pre_topc(A_1247))), inference(cnfTransformation, [status(thm)], [f_158])).
% 19.24/10.93  tff(c_17396, plain, (![A_1329, A_1330, B_1331]: (v5_pre_topc(A_1329, A_1330, B_1331) | ~v5_pre_topc(A_1329, g1_pre_topc(u1_struct_0(A_1330), u1_pre_topc(A_1330)), B_1331) | ~v1_funct_2(A_1329, u1_struct_0(g1_pre_topc(u1_struct_0(A_1330), u1_pre_topc(A_1330))), u1_struct_0(B_1331)) | ~m1_subset_1(A_1329, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1330), u1_struct_0(B_1331)))) | ~v1_funct_2(A_1329, u1_struct_0(A_1330), u1_struct_0(B_1331)) | ~v1_funct_1(A_1329) | ~l1_pre_topc(B_1331) | ~v2_pre_topc(B_1331) | ~l1_pre_topc(A_1330) | ~v2_pre_topc(A_1330) | ~r1_tarski(A_1329, k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1330), u1_pre_topc(A_1330))), u1_struct_0(B_1331))))), inference(resolution, [status(thm)], [c_18, c_15794])).
% 19.24/10.93  tff(c_17405, plain, (![A_1329, B_1331]: (v5_pre_topc(A_1329, '#skF_1', B_1331) | ~v5_pre_topc(A_1329, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_1331) | ~v1_funct_2(A_1329, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_1331)) | ~m1_subset_1(A_1329, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_1331)))) | ~v1_funct_2(A_1329, u1_struct_0('#skF_1'), u1_struct_0(B_1331)) | ~v1_funct_1(A_1329) | ~l1_pre_topc(B_1331) | ~v2_pre_topc(B_1331) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(A_1329, k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(B_1331))))), inference(superposition, [status(thm), theory('equality')], [c_8242, c_17396])).
% 19.24/10.93  tff(c_18046, plain, (![A_1375, B_1376]: (v5_pre_topc(A_1375, '#skF_1', B_1376) | ~v5_pre_topc(A_1375, g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), B_1376) | ~m1_subset_1(A_1375, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_1376)))) | ~v1_funct_2(A_1375, k1_relat_1('#skF_4'), u1_struct_0(B_1376)) | ~v1_funct_1(A_1375) | ~l1_pre_topc(B_1376) | ~v2_pre_topc(B_1376) | ~r1_tarski(A_1375, k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_1376))))), inference(demodulation, [status(thm), theory('equality')], [c_16135, c_94, c_92, c_8242, c_8242, c_16135, c_8242, c_8242, c_17405])).
% 19.24/10.93  tff(c_18055, plain, (![A_1375]: (v5_pre_topc(A_1375, '#skF_1', '#skF_2') | ~v5_pre_topc(A_1375, g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), '#skF_2') | ~m1_subset_1(A_1375, k1_zfmisc_1('#skF_4')) | ~v1_funct_2(A_1375, k1_relat_1('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(A_1375) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~r1_tarski(A_1375, k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_15535, c_18046])).
% 19.24/10.93  tff(c_18149, plain, (![A_1379]: (v5_pre_topc(A_1379, '#skF_1', '#skF_2') | ~v5_pre_topc(A_1379, g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), '#skF_2') | ~m1_subset_1(A_1379, k1_zfmisc_1('#skF_4')) | ~v1_funct_2(A_1379, k1_relat_1('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(A_1379) | ~r1_tarski(A_1379, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_15535, c_90, c_88, c_18055])).
% 19.24/10.93  tff(c_18163, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4')) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_17044, c_18149])).
% 19.24/10.93  tff(c_18173, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_80, c_8254, c_15538, c_18163])).
% 19.24/10.93  tff(c_18175, plain, $false, inference(negUnitSimplification, [status(thm)], [c_551, c_18173])).
% 19.24/10.93  tff(c_18176, plain, (k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))='#skF_4'), inference(splitRight, [status(thm)], [c_15820])).
% 19.24/10.93  tff(c_18573, plain, (k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), k1_xboole_0)='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_18569, c_18176])).
% 19.24/10.93  tff(c_18783, plain, (k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_18573, c_10])).
% 19.24/10.93  tff(c_18805, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15695, c_18783])).
% 19.24/10.93  tff(c_18806, plain, (u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_18194])).
% 19.24/10.93  tff(c_19101, plain, (k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_18806, c_18176])).
% 19.24/10.93  tff(c_18814, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_18806, c_8255])).
% 19.24/10.93  tff(c_21219, plain, (![A_1508, A_1509, B_1510]: (v5_pre_topc(A_1508, A_1509, B_1510) | ~v5_pre_topc(A_1508, g1_pre_topc(u1_struct_0(A_1509), u1_pre_topc(A_1509)), B_1510) | ~v1_funct_2(A_1508, u1_struct_0(g1_pre_topc(u1_struct_0(A_1509), u1_pre_topc(A_1509))), u1_struct_0(B_1510)) | ~m1_subset_1(A_1508, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1509), u1_struct_0(B_1510)))) | ~v1_funct_2(A_1508, u1_struct_0(A_1509), u1_struct_0(B_1510)) | ~v1_funct_1(A_1508) | ~l1_pre_topc(B_1510) | ~v2_pre_topc(B_1510) | ~l1_pre_topc(A_1509) | ~v2_pre_topc(A_1509) | ~r1_tarski(A_1508, k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1509), u1_pre_topc(A_1509))), u1_struct_0(B_1510))))), inference(resolution, [status(thm)], [c_18, c_15794])).
% 19.24/10.93  tff(c_21228, plain, (![A_1508, B_1510]: (v5_pre_topc(A_1508, '#skF_1', B_1510) | ~v5_pre_topc(A_1508, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_1510) | ~v1_funct_2(A_1508, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_1510)) | ~m1_subset_1(A_1508, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_1510)))) | ~v1_funct_2(A_1508, u1_struct_0('#skF_1'), u1_struct_0(B_1510)) | ~v1_funct_1(A_1508) | ~l1_pre_topc(B_1510) | ~v2_pre_topc(B_1510) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(A_1508, k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(B_1510))))), inference(superposition, [status(thm), theory('equality')], [c_8242, c_21219])).
% 19.24/10.93  tff(c_21933, plain, (![A_1549, B_1550]: (v5_pre_topc(A_1549, '#skF_1', B_1550) | ~v5_pre_topc(A_1549, g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), B_1550) | ~m1_subset_1(A_1549, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_1550)))) | ~v1_funct_2(A_1549, k1_relat_1('#skF_4'), u1_struct_0(B_1550)) | ~v1_funct_1(A_1549) | ~l1_pre_topc(B_1550) | ~v2_pre_topc(B_1550) | ~r1_tarski(A_1549, k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_1550))))), inference(demodulation, [status(thm), theory('equality')], [c_18806, c_94, c_92, c_8242, c_8242, c_18806, c_8242, c_8242, c_21228])).
% 19.24/10.93  tff(c_22033, plain, (![A_1554, B_1555]: (v5_pre_topc(A_1554, '#skF_1', B_1555) | ~v5_pre_topc(A_1554, g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), B_1555) | ~v1_funct_2(A_1554, k1_relat_1('#skF_4'), u1_struct_0(B_1555)) | ~v1_funct_1(A_1554) | ~l1_pre_topc(B_1555) | ~v2_pre_topc(B_1555) | ~r1_tarski(A_1554, k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_1555))))), inference(resolution, [status(thm)], [c_18, c_21933])).
% 19.24/10.93  tff(c_22074, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~r1_tarski('#skF_4', k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))))), inference(resolution, [status(thm)], [c_8247, c_22033])).
% 19.24/10.93  tff(c_22108, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_19101, c_80, c_18814, c_22074])).
% 19.24/10.93  tff(c_22109, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_22108])).
% 19.24/10.93  tff(c_22112, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_62, c_22109])).
% 19.24/10.93  tff(c_22116, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_22112])).
% 19.24/10.93  tff(c_22117, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_22108])).
% 19.24/10.93  tff(c_22119, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_22117])).
% 19.24/10.93  tff(c_22122, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_473, c_22119])).
% 19.24/10.93  tff(c_22126, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_22122])).
% 19.24/10.93  tff(c_22127, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_22117])).
% 19.24/10.93  tff(c_8684, plain, (![C_786, A_787, B_788]: (v1_funct_2(C_786, A_787, B_788) | ~v1_partfun1(C_786, A_787) | ~v1_funct_1(C_786) | ~m1_subset_1(C_786, k1_zfmisc_1(k2_zfmisc_1(A_787, B_788))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 19.24/10.93  tff(c_19072, plain, (![A_1422, A_1423, B_1424]: (v1_funct_2(A_1422, A_1423, B_1424) | ~v1_partfun1(A_1422, A_1423) | ~v1_funct_1(A_1422) | ~r1_tarski(A_1422, k2_zfmisc_1(A_1423, B_1424)))), inference(resolution, [status(thm)], [c_18, c_8684])).
% 19.24/10.93  tff(c_19099, plain, (![A_1423, B_1424]: (v1_funct_2(k2_zfmisc_1(A_1423, B_1424), A_1423, B_1424) | ~v1_partfun1(k2_zfmisc_1(A_1423, B_1424), A_1423) | ~v1_funct_1(k2_zfmisc_1(A_1423, B_1424)))), inference(resolution, [status(thm)], [c_6, c_19072])).
% 19.24/10.93  tff(c_19036, plain, (![D_1417, A_1418, B_1419]: (v5_pre_topc(D_1417, A_1418, B_1419) | ~v5_pre_topc(D_1417, A_1418, g1_pre_topc(u1_struct_0(B_1419), u1_pre_topc(B_1419))) | ~m1_subset_1(D_1417, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1418), u1_struct_0(g1_pre_topc(u1_struct_0(B_1419), u1_pre_topc(B_1419)))))) | ~v1_funct_2(D_1417, u1_struct_0(A_1418), u1_struct_0(g1_pre_topc(u1_struct_0(B_1419), u1_pre_topc(B_1419)))) | ~m1_subset_1(D_1417, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1418), u1_struct_0(B_1419)))) | ~v1_funct_2(D_1417, u1_struct_0(A_1418), u1_struct_0(B_1419)) | ~v1_funct_1(D_1417) | ~l1_pre_topc(B_1419) | ~v2_pre_topc(B_1419) | ~l1_pre_topc(A_1418) | ~v2_pre_topc(A_1418))), inference(cnfTransformation, [status(thm)], [f_187])).
% 19.24/10.93  tff(c_20997, plain, (![A_1495, A_1496, B_1497]: (v5_pre_topc(A_1495, A_1496, B_1497) | ~v5_pre_topc(A_1495, A_1496, g1_pre_topc(u1_struct_0(B_1497), u1_pre_topc(B_1497))) | ~v1_funct_2(A_1495, u1_struct_0(A_1496), u1_struct_0(g1_pre_topc(u1_struct_0(B_1497), u1_pre_topc(B_1497)))) | ~m1_subset_1(A_1495, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1496), u1_struct_0(B_1497)))) | ~v1_funct_2(A_1495, u1_struct_0(A_1496), u1_struct_0(B_1497)) | ~v1_funct_1(A_1495) | ~l1_pre_topc(B_1497) | ~v2_pre_topc(B_1497) | ~l1_pre_topc(A_1496) | ~v2_pre_topc(A_1496) | ~r1_tarski(A_1495, k2_zfmisc_1(u1_struct_0(A_1496), u1_struct_0(g1_pre_topc(u1_struct_0(B_1497), u1_pre_topc(B_1497))))))), inference(resolution, [status(thm)], [c_18, c_19036])).
% 19.24/10.93  tff(c_21006, plain, (![A_1495, B_1497]: (v5_pre_topc(A_1495, '#skF_1', B_1497) | ~v5_pre_topc(A_1495, '#skF_1', g1_pre_topc(u1_struct_0(B_1497), u1_pre_topc(B_1497))) | ~v1_funct_2(A_1495, u1_struct_0('#skF_1'), u1_struct_0(g1_pre_topc(u1_struct_0(B_1497), u1_pre_topc(B_1497)))) | ~m1_subset_1(A_1495, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_1497)))) | ~v1_funct_2(A_1495, u1_struct_0('#skF_1'), u1_struct_0(B_1497)) | ~v1_funct_1(A_1495) | ~l1_pre_topc(B_1497) | ~v2_pre_topc(B_1497) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(A_1495, k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0(B_1497), u1_pre_topc(B_1497))))))), inference(superposition, [status(thm), theory('equality')], [c_8242, c_20997])).
% 19.24/10.93  tff(c_23342, plain, (![A_1593, B_1594]: (v5_pre_topc(A_1593, '#skF_1', B_1594) | ~v5_pre_topc(A_1593, '#skF_1', g1_pre_topc(u1_struct_0(B_1594), u1_pre_topc(B_1594))) | ~v1_funct_2(A_1593, k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0(B_1594), u1_pre_topc(B_1594)))) | ~m1_subset_1(A_1593, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_1594)))) | ~v1_funct_2(A_1593, k1_relat_1('#skF_4'), u1_struct_0(B_1594)) | ~v1_funct_1(A_1593) | ~l1_pre_topc(B_1594) | ~v2_pre_topc(B_1594) | ~r1_tarski(A_1593, k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0(B_1594), u1_pre_topc(B_1594))))))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_8242, c_8242, c_8242, c_21006])).
% 19.24/10.93  tff(c_23345, plain, (![A_1593]: (v5_pre_topc(A_1593, '#skF_1', '#skF_2') | ~v5_pre_topc(A_1593, '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2(A_1593, k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1(A_1593, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(A_1593, k1_relat_1('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(A_1593) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~r1_tarski(A_1593, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_19101, c_23342])).
% 19.24/10.93  tff(c_23370, plain, (![A_1595]: (v5_pre_topc(A_1595, '#skF_1', '#skF_2') | ~v5_pre_topc(A_1595, '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2(A_1595, k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1(A_1595, k1_zfmisc_1('#skF_4')) | ~v1_funct_2(A_1595, k1_relat_1('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(A_1595) | ~r1_tarski(A_1595, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_15535, c_23345])).
% 19.24/10.93  tff(c_23386, plain, (v5_pre_topc(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), '#skF_1', '#skF_2') | ~v5_pre_topc(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_subset_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), k1_zfmisc_1('#skF_4')) | ~v1_funct_2(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), k1_relat_1('#skF_4'), u1_struct_0('#skF_2')) | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), '#skF_4') | ~v1_partfun1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), k1_relat_1('#skF_4')) | ~v1_funct_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))))), inference(resolution, [status(thm)], [c_19099, c_23370])).
% 19.24/10.93  tff(c_23408, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_19101, c_8285, c_19101, c_6, c_19101, c_8254, c_19101, c_15538, c_19101, c_22127, c_19101, c_19101, c_23386])).
% 19.24/10.93  tff(c_23410, plain, $false, inference(negUnitSimplification, [status(thm)], [c_551, c_23408])).
% 19.24/10.93  tff(c_23412, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_15587])).
% 19.24/10.93  tff(c_23456, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_23412, c_23412, c_24])).
% 19.24/10.93  tff(c_23532, plain, (v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_23456, c_8275])).
% 19.24/10.93  tff(c_23529, plain, (l1_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_23456, c_8281])).
% 19.24/10.93  tff(c_8404, plain, (![A_748, B_749, C_750]: (k1_relset_1(A_748, B_749, C_750)=k1_relat_1(C_750) | ~m1_subset_1(C_750, k1_zfmisc_1(k2_zfmisc_1(A_748, B_749))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 19.24/10.93  tff(c_8415, plain, (![A_748, B_749]: (k1_relset_1(A_748, B_749, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_8404])).
% 19.24/10.93  tff(c_8425, plain, (![A_748, B_749]: (k1_relset_1(A_748, B_749, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_8415])).
% 19.24/10.93  tff(c_8524, plain, (![C_763, B_764]: (v1_funct_2(C_763, k1_xboole_0, B_764) | k1_relset_1(k1_xboole_0, B_764, C_763)!=k1_xboole_0 | ~m1_subset_1(C_763, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_44])).
% 19.24/10.93  tff(c_8530, plain, (![B_764]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_764) | k1_relset_1(k1_xboole_0, B_764, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_8524])).
% 19.24/10.93  tff(c_8534, plain, (![B_764]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_764))), inference(demodulation, [status(thm), theory('equality')], [c_8425, c_8530])).
% 19.24/10.93  tff(c_23425, plain, (![B_764]: (v1_funct_2('#skF_4', '#skF_4', B_764))), inference(demodulation, [status(thm), theory('equality')], [c_23412, c_23412, c_8534])).
% 19.24/10.93  tff(c_23528, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_23456, c_8255])).
% 19.24/10.93  tff(c_13155, plain, (![B_1071, A_1072]: (k1_xboole_0=B_1071 | k1_relset_1(A_1072, B_1071, k1_xboole_0)=A_1072 | ~v1_funct_2(k1_xboole_0, A_1072, B_1071))), inference(resolution, [status(thm)], [c_14, c_13141])).
% 19.24/10.93  tff(c_13170, plain, (![B_1071, A_1072]: (k1_xboole_0=B_1071 | k1_xboole_0=A_1072 | ~v1_funct_2(k1_xboole_0, A_1072, B_1071))), inference(demodulation, [status(thm), theory('equality')], [c_8425, c_13155])).
% 19.24/10.93  tff(c_24200, plain, (![B_1652, A_1653]: (B_1652='#skF_4' | A_1653='#skF_4' | ~v1_funct_2('#skF_4', A_1653, B_1652))), inference(demodulation, [status(thm), theory('equality')], [c_23412, c_23412, c_23412, c_13170])).
% 19.24/10.93  tff(c_24218, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))='#skF_4' | u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')))='#skF_4'), inference(resolution, [status(thm)], [c_23528, c_24200])).
% 19.24/10.93  tff(c_24229, plain, (u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')))='#skF_4'), inference(splitLeft, [status(thm)], [c_24218])).
% 19.24/10.93  tff(c_23453, plain, (![A_5]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_23412, c_14])).
% 19.24/10.93  tff(c_23518, plain, (v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_23456, c_8247])).
% 19.24/10.93  tff(c_23523, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))))), inference(demodulation, [status(thm), theory('equality')], [c_23456, c_8253])).
% 19.24/10.93  tff(c_70, plain, (![D_64, A_50, B_58]: (v5_pre_topc(D_64, A_50, B_58) | ~v5_pre_topc(D_64, A_50, g1_pre_topc(u1_struct_0(B_58), u1_pre_topc(B_58))) | ~m1_subset_1(D_64, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_50), u1_struct_0(g1_pre_topc(u1_struct_0(B_58), u1_pre_topc(B_58)))))) | ~v1_funct_2(D_64, u1_struct_0(A_50), u1_struct_0(g1_pre_topc(u1_struct_0(B_58), u1_pre_topc(B_58)))) | ~m1_subset_1(D_64, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_50), u1_struct_0(B_58)))) | ~v1_funct_2(D_64, u1_struct_0(A_50), u1_struct_0(B_58)) | ~v1_funct_1(D_64) | ~l1_pre_topc(B_58) | ~v2_pre_topc(B_58) | ~l1_pre_topc(A_50) | ~v2_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_187])).
% 19.24/10.93  tff(c_23779, plain, (v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), '#skF_2') | ~v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_23523, c_70])).
% 19.24/10.93  tff(c_23805, plain, (v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), '#skF_2') | ~v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), u1_struct_0('#skF_2')) | ~l1_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_80, c_23528, c_23779])).
% 19.24/10.93  tff(c_24885, plain, (v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_23532, c_23529, c_23425, c_24229, c_23453, c_23518, c_23805])).
% 19.24/10.93  tff(c_23454, plain, (![B_4]: (k2_zfmisc_1('#skF_4', B_4)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_23412, c_23412, c_12])).
% 19.24/10.93  tff(c_23536, plain, (u1_struct_0('#skF_1')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_23456, c_8242])).
% 19.24/10.93  tff(c_23549, plain, (![D_1597, A_1598, B_1599]: (v5_pre_topc(D_1597, A_1598, B_1599) | ~v5_pre_topc(D_1597, g1_pre_topc(u1_struct_0(A_1598), u1_pre_topc(A_1598)), B_1599) | ~m1_subset_1(D_1597, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1598), u1_pre_topc(A_1598))), u1_struct_0(B_1599)))) | ~v1_funct_2(D_1597, u1_struct_0(g1_pre_topc(u1_struct_0(A_1598), u1_pre_topc(A_1598))), u1_struct_0(B_1599)) | ~m1_subset_1(D_1597, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1598), u1_struct_0(B_1599)))) | ~v1_funct_2(D_1597, u1_struct_0(A_1598), u1_struct_0(B_1599)) | ~v1_funct_1(D_1597) | ~l1_pre_topc(B_1599) | ~v2_pre_topc(B_1599) | ~l1_pre_topc(A_1598) | ~v2_pre_topc(A_1598))), inference(cnfTransformation, [status(thm)], [f_158])).
% 19.24/10.93  tff(c_24347, plain, (![A_1657, A_1658, B_1659]: (v5_pre_topc(A_1657, A_1658, B_1659) | ~v5_pre_topc(A_1657, g1_pre_topc(u1_struct_0(A_1658), u1_pre_topc(A_1658)), B_1659) | ~v1_funct_2(A_1657, u1_struct_0(g1_pre_topc(u1_struct_0(A_1658), u1_pre_topc(A_1658))), u1_struct_0(B_1659)) | ~m1_subset_1(A_1657, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1658), u1_struct_0(B_1659)))) | ~v1_funct_2(A_1657, u1_struct_0(A_1658), u1_struct_0(B_1659)) | ~v1_funct_1(A_1657) | ~l1_pre_topc(B_1659) | ~v2_pre_topc(B_1659) | ~l1_pre_topc(A_1658) | ~v2_pre_topc(A_1658) | ~r1_tarski(A_1657, k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1658), u1_pre_topc(A_1658))), u1_struct_0(B_1659))))), inference(resolution, [status(thm)], [c_18, c_23549])).
% 19.24/10.93  tff(c_24830, plain, (![A_1709, B_1710]: (v5_pre_topc(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1709), u1_pre_topc(A_1709))), u1_struct_0(B_1710)), A_1709, B_1710) | ~v5_pre_topc(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1709), u1_pre_topc(A_1709))), u1_struct_0(B_1710)), g1_pre_topc(u1_struct_0(A_1709), u1_pre_topc(A_1709)), B_1710) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1709), u1_pre_topc(A_1709))), u1_struct_0(B_1710)), u1_struct_0(g1_pre_topc(u1_struct_0(A_1709), u1_pre_topc(A_1709))), u1_struct_0(B_1710)) | ~m1_subset_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1709), u1_pre_topc(A_1709))), u1_struct_0(B_1710)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1709), u1_struct_0(B_1710)))) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1709), u1_pre_topc(A_1709))), u1_struct_0(B_1710)), u1_struct_0(A_1709), u1_struct_0(B_1710)) | ~v1_funct_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1709), u1_pre_topc(A_1709))), u1_struct_0(B_1710))) | ~l1_pre_topc(B_1710) | ~v2_pre_topc(B_1710) | ~l1_pre_topc(A_1709) | ~v2_pre_topc(A_1709))), inference(resolution, [status(thm)], [c_6, c_24347])).
% 19.24/10.93  tff(c_24851, plain, (![B_1710]: (v5_pre_topc(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_1710)), '#skF_1', B_1710) | ~v5_pre_topc(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_1710)), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_1710) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), u1_struct_0(B_1710)), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_1710)) | ~m1_subset_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_1710)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_1710)))) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_1710)), u1_struct_0('#skF_1'), u1_struct_0(B_1710)) | ~v1_funct_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_1710))) | ~l1_pre_topc(B_1710) | ~v2_pre_topc(B_1710) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_23536, c_24830])).
% 19.24/10.93  tff(c_24872, plain, (![B_1710]: (v5_pre_topc('#skF_4', '#skF_1', B_1710) | ~v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), B_1710) | ~l1_pre_topc(B_1710) | ~v2_pre_topc(B_1710))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_80, c_23454, c_24229, c_23536, c_23425, c_23454, c_24229, c_23536, c_23536, c_23453, c_23454, c_24229, c_23454, c_23536, c_23536, c_23425, c_24229, c_23454, c_24229, c_23536, c_23454, c_24229, c_23536, c_23536, c_23454, c_24229, c_23536, c_24851])).
% 19.24/10.93  tff(c_24888, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24885, c_24872])).
% 19.24/10.93  tff(c_24891, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_24888])).
% 19.24/10.93  tff(c_24893, plain, $false, inference(negUnitSimplification, [status(thm)], [c_551, c_24891])).
% 19.24/10.93  tff(c_24894, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))='#skF_4'), inference(splitRight, [status(thm)], [c_24218])).
% 19.24/10.93  tff(c_60, plain, (![A_33]: (m1_subset_1(u1_pre_topc(A_33), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_33)))) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_121])).
% 19.24/10.93  tff(c_498, plain, (![A_138, B_139]: (v1_pre_topc(g1_pre_topc(A_138, B_139)) | ~m1_subset_1(B_139, k1_zfmisc_1(k1_zfmisc_1(A_138))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 19.24/10.93  tff(c_510, plain, (![A_33]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_33), u1_pre_topc(A_33))) | ~l1_pre_topc(A_33))), inference(resolution, [status(thm)], [c_60, c_498])).
% 19.24/10.93  tff(c_24975, plain, (v1_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_24894, c_510])).
% 19.24/10.93  tff(c_25481, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_24975])).
% 19.24/10.93  tff(c_25484, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_473, c_25481])).
% 19.24/10.93  tff(c_25488, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_25484])).
% 19.24/10.93  tff(c_25490, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_24975])).
% 19.24/10.93  tff(c_24972, plain, (v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_24894, c_62])).
% 19.24/10.93  tff(c_25803, plain, (v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_25490, c_24972])).
% 19.24/10.93  tff(c_25804, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_25803])).
% 19.24/10.93  tff(c_25808, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_62, c_25804])).
% 19.24/10.93  tff(c_25812, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_25808])).
% 19.24/10.93  tff(c_25814, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_25803])).
% 19.24/10.93  tff(c_23649, plain, (![D_1602, A_1603, B_1604]: (v5_pre_topc(D_1602, A_1603, B_1604) | ~v5_pre_topc(D_1602, A_1603, g1_pre_topc(u1_struct_0(B_1604), u1_pre_topc(B_1604))) | ~m1_subset_1(D_1602, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1603), u1_struct_0(g1_pre_topc(u1_struct_0(B_1604), u1_pre_topc(B_1604)))))) | ~v1_funct_2(D_1602, u1_struct_0(A_1603), u1_struct_0(g1_pre_topc(u1_struct_0(B_1604), u1_pre_topc(B_1604)))) | ~m1_subset_1(D_1602, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1603), u1_struct_0(B_1604)))) | ~v1_funct_2(D_1602, u1_struct_0(A_1603), u1_struct_0(B_1604)) | ~v1_funct_1(D_1602) | ~l1_pre_topc(B_1604) | ~v2_pre_topc(B_1604) | ~l1_pre_topc(A_1603) | ~v2_pre_topc(A_1603))), inference(cnfTransformation, [status(thm)], [f_187])).
% 19.24/10.93  tff(c_25020, plain, (![A_1713, A_1714, B_1715]: (v5_pre_topc(A_1713, A_1714, B_1715) | ~v5_pre_topc(A_1713, A_1714, g1_pre_topc(u1_struct_0(B_1715), u1_pre_topc(B_1715))) | ~v1_funct_2(A_1713, u1_struct_0(A_1714), u1_struct_0(g1_pre_topc(u1_struct_0(B_1715), u1_pre_topc(B_1715)))) | ~m1_subset_1(A_1713, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1714), u1_struct_0(B_1715)))) | ~v1_funct_2(A_1713, u1_struct_0(A_1714), u1_struct_0(B_1715)) | ~v1_funct_1(A_1713) | ~l1_pre_topc(B_1715) | ~v2_pre_topc(B_1715) | ~l1_pre_topc(A_1714) | ~v2_pre_topc(A_1714) | ~r1_tarski(A_1713, k2_zfmisc_1(u1_struct_0(A_1714), u1_struct_0(g1_pre_topc(u1_struct_0(B_1715), u1_pre_topc(B_1715))))))), inference(resolution, [status(thm)], [c_18, c_23649])).
% 19.24/10.93  tff(c_25821, plain, (![A_1785, B_1786]: (v5_pre_topc(k2_zfmisc_1(u1_struct_0(A_1785), u1_struct_0(g1_pre_topc(u1_struct_0(B_1786), u1_pre_topc(B_1786)))), A_1785, B_1786) | ~v5_pre_topc(k2_zfmisc_1(u1_struct_0(A_1785), u1_struct_0(g1_pre_topc(u1_struct_0(B_1786), u1_pre_topc(B_1786)))), A_1785, g1_pre_topc(u1_struct_0(B_1786), u1_pre_topc(B_1786))) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(A_1785), u1_struct_0(g1_pre_topc(u1_struct_0(B_1786), u1_pre_topc(B_1786)))), u1_struct_0(A_1785), u1_struct_0(g1_pre_topc(u1_struct_0(B_1786), u1_pre_topc(B_1786)))) | ~m1_subset_1(k2_zfmisc_1(u1_struct_0(A_1785), u1_struct_0(g1_pre_topc(u1_struct_0(B_1786), u1_pre_topc(B_1786)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1785), u1_struct_0(B_1786)))) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(A_1785), u1_struct_0(g1_pre_topc(u1_struct_0(B_1786), u1_pre_topc(B_1786)))), u1_struct_0(A_1785), u1_struct_0(B_1786)) | ~v1_funct_1(k2_zfmisc_1(u1_struct_0(A_1785), u1_struct_0(g1_pre_topc(u1_struct_0(B_1786), u1_pre_topc(B_1786))))) | ~l1_pre_topc(B_1786) | ~v2_pre_topc(B_1786) | ~l1_pre_topc(A_1785) | ~v2_pre_topc(A_1785))), inference(resolution, [status(thm)], [c_6, c_25020])).
% 19.24/10.93  tff(c_25848, plain, (![B_1786]: (v5_pre_topc(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(g1_pre_topc(u1_struct_0(B_1786), u1_pre_topc(B_1786)))), '#skF_1', B_1786) | ~v5_pre_topc(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(g1_pre_topc(u1_struct_0(B_1786), u1_pre_topc(B_1786)))), '#skF_1', g1_pre_topc(u1_struct_0(B_1786), u1_pre_topc(B_1786))) | ~v1_funct_2(k2_zfmisc_1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(B_1786), u1_pre_topc(B_1786)))), u1_struct_0('#skF_1'), u1_struct_0(g1_pre_topc(u1_struct_0(B_1786), u1_pre_topc(B_1786)))) | ~m1_subset_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(g1_pre_topc(u1_struct_0(B_1786), u1_pre_topc(B_1786)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_1786)))) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(g1_pre_topc(u1_struct_0(B_1786), u1_pre_topc(B_1786)))), u1_struct_0('#skF_1'), u1_struct_0(B_1786)) | ~v1_funct_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(g1_pre_topc(u1_struct_0(B_1786), u1_pre_topc(B_1786))))) | ~l1_pre_topc(B_1786) | ~v2_pre_topc(B_1786) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_23536, c_25821])).
% 19.24/10.93  tff(c_25880, plain, (![B_1787]: (v5_pre_topc('#skF_4', '#skF_1', B_1787) | ~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0(B_1787), u1_pre_topc(B_1787))) | ~l1_pre_topc(B_1787) | ~v2_pre_topc(B_1787))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_80, c_23454, c_23536, c_23425, c_23536, c_23454, c_23536, c_23453, c_23454, c_23536, c_23425, c_23536, c_23454, c_23454, c_23536, c_23454, c_23536, c_25848])).
% 19.24/10.93  tff(c_25886, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_24894, c_25880])).
% 19.24/10.93  tff(c_25892, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))))), inference(demodulation, [status(thm), theory('equality')], [c_25814, c_25490, c_25886])).
% 19.24/10.93  tff(c_25896, plain, (~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))))), inference(splitLeft, [status(thm)], [c_25892])).
% 19.24/10.93  tff(c_23912, plain, (![D_1611, A_1612, B_1613]: (v5_pre_topc(D_1611, A_1612, g1_pre_topc(u1_struct_0(B_1613), u1_pre_topc(B_1613))) | ~v5_pre_topc(D_1611, A_1612, B_1613) | ~m1_subset_1(D_1611, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1612), u1_struct_0(g1_pre_topc(u1_struct_0(B_1613), u1_pre_topc(B_1613)))))) | ~v1_funct_2(D_1611, u1_struct_0(A_1612), u1_struct_0(g1_pre_topc(u1_struct_0(B_1613), u1_pre_topc(B_1613)))) | ~m1_subset_1(D_1611, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1612), u1_struct_0(B_1613)))) | ~v1_funct_2(D_1611, u1_struct_0(A_1612), u1_struct_0(B_1613)) | ~v1_funct_1(D_1611) | ~l1_pre_topc(B_1613) | ~v2_pre_topc(B_1613) | ~l1_pre_topc(A_1612) | ~v2_pre_topc(A_1612))), inference(cnfTransformation, [status(thm)], [f_187])).
% 19.24/10.93  tff(c_24166, plain, (![A_1647, A_1648, B_1649]: (v5_pre_topc(A_1647, A_1648, g1_pre_topc(u1_struct_0(B_1649), u1_pre_topc(B_1649))) | ~v5_pre_topc(A_1647, A_1648, B_1649) | ~v1_funct_2(A_1647, u1_struct_0(A_1648), u1_struct_0(g1_pre_topc(u1_struct_0(B_1649), u1_pre_topc(B_1649)))) | ~m1_subset_1(A_1647, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1648), u1_struct_0(B_1649)))) | ~v1_funct_2(A_1647, u1_struct_0(A_1648), u1_struct_0(B_1649)) | ~v1_funct_1(A_1647) | ~l1_pre_topc(B_1649) | ~v2_pre_topc(B_1649) | ~l1_pre_topc(A_1648) | ~v2_pre_topc(A_1648) | ~r1_tarski(A_1647, k2_zfmisc_1(u1_struct_0(A_1648), u1_struct_0(g1_pre_topc(u1_struct_0(B_1649), u1_pre_topc(B_1649))))))), inference(resolution, [status(thm)], [c_18, c_23912])).
% 19.24/10.93  tff(c_25515, plain, (![A_1764, B_1765]: (v5_pre_topc(k2_zfmisc_1(u1_struct_0(A_1764), u1_struct_0(g1_pre_topc(u1_struct_0(B_1765), u1_pre_topc(B_1765)))), A_1764, g1_pre_topc(u1_struct_0(B_1765), u1_pre_topc(B_1765))) | ~v5_pre_topc(k2_zfmisc_1(u1_struct_0(A_1764), u1_struct_0(g1_pre_topc(u1_struct_0(B_1765), u1_pre_topc(B_1765)))), A_1764, B_1765) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(A_1764), u1_struct_0(g1_pre_topc(u1_struct_0(B_1765), u1_pre_topc(B_1765)))), u1_struct_0(A_1764), u1_struct_0(g1_pre_topc(u1_struct_0(B_1765), u1_pre_topc(B_1765)))) | ~m1_subset_1(k2_zfmisc_1(u1_struct_0(A_1764), u1_struct_0(g1_pre_topc(u1_struct_0(B_1765), u1_pre_topc(B_1765)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1764), u1_struct_0(B_1765)))) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(A_1764), u1_struct_0(g1_pre_topc(u1_struct_0(B_1765), u1_pre_topc(B_1765)))), u1_struct_0(A_1764), u1_struct_0(B_1765)) | ~v1_funct_1(k2_zfmisc_1(u1_struct_0(A_1764), u1_struct_0(g1_pre_topc(u1_struct_0(B_1765), u1_pre_topc(B_1765))))) | ~l1_pre_topc(B_1765) | ~v2_pre_topc(B_1765) | ~l1_pre_topc(A_1764) | ~v2_pre_topc(A_1764))), inference(resolution, [status(thm)], [c_6, c_24166])).
% 19.24/10.93  tff(c_25542, plain, (![B_1765]: (v5_pre_topc(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(g1_pre_topc(u1_struct_0(B_1765), u1_pre_topc(B_1765)))), '#skF_1', g1_pre_topc(u1_struct_0(B_1765), u1_pre_topc(B_1765))) | ~v5_pre_topc(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(g1_pre_topc(u1_struct_0(B_1765), u1_pre_topc(B_1765)))), '#skF_1', B_1765) | ~v1_funct_2(k2_zfmisc_1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(B_1765), u1_pre_topc(B_1765)))), u1_struct_0('#skF_1'), u1_struct_0(g1_pre_topc(u1_struct_0(B_1765), u1_pre_topc(B_1765)))) | ~m1_subset_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(g1_pre_topc(u1_struct_0(B_1765), u1_pre_topc(B_1765)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_1765)))) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(g1_pre_topc(u1_struct_0(B_1765), u1_pre_topc(B_1765)))), u1_struct_0('#skF_1'), u1_struct_0(B_1765)) | ~v1_funct_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(g1_pre_topc(u1_struct_0(B_1765), u1_pre_topc(B_1765))))) | ~l1_pre_topc(B_1765) | ~v2_pre_topc(B_1765) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_23536, c_25515])).
% 19.24/10.93  tff(c_25574, plain, (![B_1766]: (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0(B_1766), u1_pre_topc(B_1766))) | ~v5_pre_topc('#skF_4', '#skF_1', B_1766) | ~l1_pre_topc(B_1766) | ~v2_pre_topc(B_1766))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_80, c_23454, c_23536, c_23425, c_23536, c_23454, c_23536, c_23453, c_23454, c_23536, c_23425, c_23536, c_23454, c_23454, c_23536, c_23454, c_23536, c_25542])).
% 19.24/10.93  tff(c_25577, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_24894, c_25574])).
% 19.24/10.93  tff(c_25582, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_25490, c_25577])).
% 19.24/10.93  tff(c_26035, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_25814, c_25582])).
% 19.24/10.93  tff(c_26036, plain, (~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_25896, c_26035])).
% 19.24/10.93  tff(c_24896, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_24894, c_23528])).
% 19.24/10.93  tff(c_23825, plain, (![A_1608]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_1608)))), inference(demodulation, [status(thm), theory('equality')], [c_23412, c_14])).
% 19.24/10.93  tff(c_66, plain, (![D_49, A_35, B_43]: (v5_pre_topc(D_49, A_35, B_43) | ~v5_pre_topc(D_49, g1_pre_topc(u1_struct_0(A_35), u1_pre_topc(A_35)), B_43) | ~m1_subset_1(D_49, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_35), u1_pre_topc(A_35))), u1_struct_0(B_43)))) | ~v1_funct_2(D_49, u1_struct_0(g1_pre_topc(u1_struct_0(A_35), u1_pre_topc(A_35))), u1_struct_0(B_43)) | ~m1_subset_1(D_49, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_35), u1_struct_0(B_43)))) | ~v1_funct_2(D_49, u1_struct_0(A_35), u1_struct_0(B_43)) | ~v1_funct_1(D_49) | ~l1_pre_topc(B_43) | ~v2_pre_topc(B_43) | ~l1_pre_topc(A_35) | ~v2_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_158])).
% 19.24/10.93  tff(c_23833, plain, (![A_35, B_43]: (v5_pre_topc('#skF_4', A_35, B_43) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_35), u1_pre_topc(A_35)), B_43) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_35), u1_pre_topc(A_35))), u1_struct_0(B_43)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_35), u1_struct_0(B_43)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_35), u1_struct_0(B_43)) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(B_43) | ~v2_pre_topc(B_43) | ~l1_pre_topc(A_35) | ~v2_pre_topc(A_35))), inference(resolution, [status(thm)], [c_23825, c_66])).
% 19.24/10.93  tff(c_27161, plain, (![A_1836, B_1837]: (v5_pre_topc('#skF_4', A_1836, B_1837) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_1836), u1_pre_topc(A_1836)), B_1837) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_1836), u1_pre_topc(A_1836))), u1_struct_0(B_1837)) | ~v1_funct_2('#skF_4', u1_struct_0(A_1836), u1_struct_0(B_1837)) | ~l1_pre_topc(B_1837) | ~v2_pre_topc(B_1837) | ~l1_pre_topc(A_1836) | ~v2_pre_topc(A_1836))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_23453, c_23833])).
% 19.24/10.93  tff(c_27179, plain, (![B_1837]: (v5_pre_topc('#skF_4', '#skF_1', B_1837) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_1837) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), u1_struct_0(B_1837)) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0(B_1837)) | ~l1_pre_topc(B_1837) | ~v2_pre_topc(B_1837) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_23536, c_27161])).
% 19.24/10.93  tff(c_27195, plain, (![B_1838]: (v5_pre_topc('#skF_4', '#skF_1', B_1838) | ~v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), B_1838) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), u1_struct_0(B_1838)) | ~l1_pre_topc(B_1838) | ~v2_pre_topc(B_1838))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_23425, c_23536, c_23536, c_27179])).
% 19.24/10.93  tff(c_27198, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), '#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_24894, c_27195])).
% 19.24/10.93  tff(c_27209, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_25814, c_25490, c_24896, c_23518, c_27198])).
% 19.24/10.93  tff(c_27211, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26036, c_27209])).
% 19.24/10.93  tff(c_27212, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_25892])).
% 19.24/10.93  tff(c_25873, plain, (![B_1786]: (v5_pre_topc('#skF_4', '#skF_1', B_1786) | ~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0(B_1786), u1_pre_topc(B_1786))) | ~l1_pre_topc(B_1786) | ~v2_pre_topc(B_1786))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_80, c_23454, c_23536, c_23425, c_23536, c_23454, c_23536, c_23453, c_23454, c_23536, c_23425, c_23536, c_23454, c_23454, c_23536, c_23454, c_23536, c_25848])).
% 19.24/10.93  tff(c_27216, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_27212, c_25873])).
% 19.24/10.93  tff(c_27219, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_27216])).
% 19.24/10.93  tff(c_27221, plain, $false, inference(negUnitSimplification, [status(thm)], [c_551, c_27219])).
% 19.24/10.93  tff(c_27222, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_106])).
% 19.24/10.93  tff(c_27443, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_489, c_27222])).
% 19.24/10.93  tff(c_27444, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_104])).
% 19.24/10.93  tff(c_32270, plain, (![B_4]: (k2_zfmisc_1('#skF_4', B_4)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32208, c_32208, c_12])).
% 19.24/10.93  tff(c_32272, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_32208, c_32208, c_24])).
% 19.24/10.93  tff(c_32632, plain, (u1_struct_0('#skF_1')='#skF_4' | u1_struct_0('#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_32208, c_32208, c_32207])).
% 19.24/10.93  tff(c_32633, plain, (u1_struct_0('#skF_2')='#skF_4'), inference(splitLeft, [status(thm)], [c_32632])).
% 19.24/10.93  tff(c_32638, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32633, c_103])).
% 19.24/10.93  tff(c_32271, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32208, c_32208, c_10])).
% 19.24/10.93  tff(c_32639, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_32633, c_78])).
% 19.24/10.93  tff(c_30573, plain, (![A_2122, B_2123]: (k1_relset_1(A_2122, B_2123, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_30559])).
% 19.24/10.93  tff(c_30584, plain, (![A_2122, B_2123]: (k1_relset_1(A_2122, B_2123, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_30573])).
% 19.24/10.93  tff(c_31360, plain, (![B_2196, A_2197]: (k1_xboole_0=B_2196 | k1_relset_1(A_2197, B_2196, k1_xboole_0)=A_2197 | ~v1_funct_2(k1_xboole_0, A_2197, B_2196))), inference(resolution, [status(thm)], [c_14, c_31346])).
% 19.24/10.93  tff(c_31369, plain, (![B_2196, A_2197]: (k1_xboole_0=B_2196 | k1_xboole_0=A_2197 | ~v1_funct_2(k1_xboole_0, A_2197, B_2196))), inference(demodulation, [status(thm), theory('equality')], [c_30584, c_31360])).
% 19.24/10.93  tff(c_32836, plain, (![B_2301, A_2302]: (B_2301='#skF_4' | A_2302='#skF_4' | ~v1_funct_2('#skF_4', A_2302, B_2301))), inference(demodulation, [status(thm), theory('equality')], [c_32208, c_32208, c_32208, c_31369])).
% 19.24/10.93  tff(c_32859, plain, (u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))='#skF_4' | u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))='#skF_4'), inference(resolution, [status(thm)], [c_32639, c_32836])).
% 19.24/10.93  tff(c_32876, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))='#skF_4'), inference(splitLeft, [status(thm)], [c_32859])).
% 19.24/10.93  tff(c_27614, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_405, c_27605])).
% 19.24/10.93  tff(c_27627, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_216, c_27614])).
% 19.24/10.93  tff(c_32326, plain, (~v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(splitLeft, [status(thm)], [c_27627])).
% 19.24/10.93  tff(c_32878, plain, (~v1_partfun1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32876, c_32326])).
% 19.24/10.93  tff(c_32882, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32253, c_32878])).
% 19.24/10.93  tff(c_32883, plain, (u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))='#skF_4'), inference(splitRight, [status(thm)], [c_32859])).
% 19.24/10.93  tff(c_32269, plain, (![A_5]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_32208, c_14])).
% 19.24/10.93  tff(c_32710, plain, (![D_2279, A_2280, B_2281]: (v5_pre_topc(D_2279, A_2280, g1_pre_topc(u1_struct_0(B_2281), u1_pre_topc(B_2281))) | ~v5_pre_topc(D_2279, A_2280, B_2281) | ~m1_subset_1(D_2279, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2280), u1_struct_0(g1_pre_topc(u1_struct_0(B_2281), u1_pre_topc(B_2281)))))) | ~v1_funct_2(D_2279, u1_struct_0(A_2280), u1_struct_0(g1_pre_topc(u1_struct_0(B_2281), u1_pre_topc(B_2281)))) | ~m1_subset_1(D_2279, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2280), u1_struct_0(B_2281)))) | ~v1_funct_2(D_2279, u1_struct_0(A_2280), u1_struct_0(B_2281)) | ~v1_funct_1(D_2279) | ~l1_pre_topc(B_2281) | ~v2_pre_topc(B_2281) | ~l1_pre_topc(A_2280) | ~v2_pre_topc(A_2280))), inference(cnfTransformation, [status(thm)], [f_187])).
% 19.24/10.93  tff(c_33349, plain, (![A_2346, A_2347, B_2348]: (v5_pre_topc(A_2346, A_2347, g1_pre_topc(u1_struct_0(B_2348), u1_pre_topc(B_2348))) | ~v5_pre_topc(A_2346, A_2347, B_2348) | ~v1_funct_2(A_2346, u1_struct_0(A_2347), u1_struct_0(g1_pre_topc(u1_struct_0(B_2348), u1_pre_topc(B_2348)))) | ~m1_subset_1(A_2346, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2347), u1_struct_0(B_2348)))) | ~v1_funct_2(A_2346, u1_struct_0(A_2347), u1_struct_0(B_2348)) | ~v1_funct_1(A_2346) | ~l1_pre_topc(B_2348) | ~v2_pre_topc(B_2348) | ~l1_pre_topc(A_2347) | ~v2_pre_topc(A_2347) | ~r1_tarski(A_2346, k2_zfmisc_1(u1_struct_0(A_2347), u1_struct_0(g1_pre_topc(u1_struct_0(B_2348), u1_pre_topc(B_2348))))))), inference(resolution, [status(thm)], [c_18, c_32710])).
% 19.24/10.93  tff(c_33754, plain, (![A_2383, B_2384]: (v5_pre_topc(k2_zfmisc_1(u1_struct_0(A_2383), u1_struct_0(g1_pre_topc(u1_struct_0(B_2384), u1_pre_topc(B_2384)))), A_2383, g1_pre_topc(u1_struct_0(B_2384), u1_pre_topc(B_2384))) | ~v5_pre_topc(k2_zfmisc_1(u1_struct_0(A_2383), u1_struct_0(g1_pre_topc(u1_struct_0(B_2384), u1_pre_topc(B_2384)))), A_2383, B_2384) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(A_2383), u1_struct_0(g1_pre_topc(u1_struct_0(B_2384), u1_pre_topc(B_2384)))), u1_struct_0(A_2383), u1_struct_0(g1_pre_topc(u1_struct_0(B_2384), u1_pre_topc(B_2384)))) | ~m1_subset_1(k2_zfmisc_1(u1_struct_0(A_2383), u1_struct_0(g1_pre_topc(u1_struct_0(B_2384), u1_pre_topc(B_2384)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2383), u1_struct_0(B_2384)))) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(A_2383), u1_struct_0(g1_pre_topc(u1_struct_0(B_2384), u1_pre_topc(B_2384)))), u1_struct_0(A_2383), u1_struct_0(B_2384)) | ~v1_funct_1(k2_zfmisc_1(u1_struct_0(A_2383), u1_struct_0(g1_pre_topc(u1_struct_0(B_2384), u1_pre_topc(B_2384))))) | ~l1_pre_topc(B_2384) | ~v2_pre_topc(B_2384) | ~l1_pre_topc(A_2383) | ~v2_pre_topc(A_2383))), inference(resolution, [status(thm)], [c_6, c_33349])).
% 19.24/10.93  tff(c_33784, plain, (![A_2383]: (v5_pre_topc(k2_zfmisc_1(u1_struct_0(A_2383), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), A_2383, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc(k2_zfmisc_1(u1_struct_0(A_2383), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), A_2383, '#skF_2') | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(A_2383), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), u1_struct_0(A_2383), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~m1_subset_1(k2_zfmisc_1(u1_struct_0(A_2383), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2383), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(A_2383), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), u1_struct_0(A_2383), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_zfmisc_1(u1_struct_0(A_2383), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(A_2383) | ~v2_pre_topc(A_2383))), inference(superposition, [status(thm), theory('equality')], [c_32633, c_33754])).
% 19.24/10.93  tff(c_33802, plain, (![A_2383]: (v5_pre_topc('#skF_4', A_2383, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', A_2383, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0(A_2383), '#skF_4') | ~l1_pre_topc(A_2383) | ~v2_pre_topc(A_2383))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_80, c_32271, c_32883, c_32633, c_32271, c_32883, c_32633, c_32633, c_32269, c_32271, c_32883, c_32271, c_32633, c_32633, c_32883, c_32271, c_32883, c_32633, c_32271, c_32883, c_32633, c_32271, c_32883, c_32633, c_32633, c_33784])).
% 19.24/10.93  tff(c_32885, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32883, c_32639])).
% 19.24/10.93  tff(c_32668, plain, (v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_32633, c_62])).
% 19.24/10.93  tff(c_32700, plain, (v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_32668])).
% 19.24/10.93  tff(c_32677, plain, (l1_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_32633, c_473])).
% 19.24/10.93  tff(c_32706, plain, (l1_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_32677])).
% 19.24/10.93  tff(c_32563, plain, (![D_2269, A_2270, B_2271]: (v5_pre_topc(D_2269, g1_pre_topc(u1_struct_0(A_2270), u1_pre_topc(A_2270)), B_2271) | ~v5_pre_topc(D_2269, A_2270, B_2271) | ~m1_subset_1(D_2269, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2270), u1_pre_topc(A_2270))), u1_struct_0(B_2271)))) | ~v1_funct_2(D_2269, u1_struct_0(g1_pre_topc(u1_struct_0(A_2270), u1_pre_topc(A_2270))), u1_struct_0(B_2271)) | ~m1_subset_1(D_2269, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2270), u1_struct_0(B_2271)))) | ~v1_funct_2(D_2269, u1_struct_0(A_2270), u1_struct_0(B_2271)) | ~v1_funct_1(D_2269) | ~l1_pre_topc(B_2271) | ~v2_pre_topc(B_2271) | ~l1_pre_topc(A_2270) | ~v2_pre_topc(A_2270))), inference(cnfTransformation, [status(thm)], [f_158])).
% 19.24/10.93  tff(c_33256, plain, (![A_2338, A_2339, B_2340]: (v5_pre_topc(A_2338, g1_pre_topc(u1_struct_0(A_2339), u1_pre_topc(A_2339)), B_2340) | ~v5_pre_topc(A_2338, A_2339, B_2340) | ~v1_funct_2(A_2338, u1_struct_0(g1_pre_topc(u1_struct_0(A_2339), u1_pre_topc(A_2339))), u1_struct_0(B_2340)) | ~m1_subset_1(A_2338, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2339), u1_struct_0(B_2340)))) | ~v1_funct_2(A_2338, u1_struct_0(A_2339), u1_struct_0(B_2340)) | ~v1_funct_1(A_2338) | ~l1_pre_topc(B_2340) | ~v2_pre_topc(B_2340) | ~l1_pre_topc(A_2339) | ~v2_pre_topc(A_2339) | ~r1_tarski(A_2338, k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2339), u1_pre_topc(A_2339))), u1_struct_0(B_2340))))), inference(resolution, [status(thm)], [c_18, c_32563])).
% 19.24/10.93  tff(c_33853, plain, (![A_2387, B_2388]: (v5_pre_topc(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2387), u1_pre_topc(A_2387))), u1_struct_0(B_2388)), g1_pre_topc(u1_struct_0(A_2387), u1_pre_topc(A_2387)), B_2388) | ~v5_pre_topc(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2387), u1_pre_topc(A_2387))), u1_struct_0(B_2388)), A_2387, B_2388) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2387), u1_pre_topc(A_2387))), u1_struct_0(B_2388)), u1_struct_0(g1_pre_topc(u1_struct_0(A_2387), u1_pre_topc(A_2387))), u1_struct_0(B_2388)) | ~m1_subset_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2387), u1_pre_topc(A_2387))), u1_struct_0(B_2388)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2387), u1_struct_0(B_2388)))) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2387), u1_pre_topc(A_2387))), u1_struct_0(B_2388)), u1_struct_0(A_2387), u1_struct_0(B_2388)) | ~v1_funct_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2387), u1_pre_topc(A_2387))), u1_struct_0(B_2388))) | ~l1_pre_topc(B_2388) | ~v2_pre_topc(B_2388) | ~l1_pre_topc(A_2387) | ~v2_pre_topc(A_2387))), inference(resolution, [status(thm)], [c_6, c_33256])).
% 19.24/10.93  tff(c_33865, plain, (![A_2387]: (v5_pre_topc(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2387), u1_pre_topc(A_2387))), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), g1_pre_topc(u1_struct_0(A_2387), u1_pre_topc(A_2387)), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2387), u1_pre_topc(A_2387))), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), A_2387, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2387), u1_pre_topc(A_2387))), '#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0(A_2387), u1_pre_topc(A_2387))), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~m1_subset_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2387), u1_pre_topc(A_2387))), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2387), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))))) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2387), u1_pre_topc(A_2387))), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), u1_struct_0(A_2387), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~v1_funct_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2387), u1_pre_topc(A_2387))), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))))) | ~l1_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_2387) | ~v2_pre_topc(A_2387))), inference(superposition, [status(thm), theory('equality')], [c_32883, c_33853])).
% 19.24/10.93  tff(c_34051, plain, (![A_2393]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_2393), u1_pre_topc(A_2393)), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', A_2393, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_2393), u1_pre_topc(A_2393))), '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0(A_2393), '#skF_4') | ~l1_pre_topc(A_2393) | ~v2_pre_topc(A_2393))), inference(demodulation, [status(thm), theory('equality')], [c_32700, c_32706, c_80, c_32271, c_32883, c_32883, c_32271, c_32883, c_32269, c_32271, c_32883, c_32883, c_32271, c_32271, c_32883, c_32271, c_32883, c_33865])).
% 19.24/10.93  tff(c_27470, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_27444, c_106])).
% 19.24/10.93  tff(c_32637, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_32633, c_27470])).
% 19.24/10.93  tff(c_34064, plain, (~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34051, c_32637])).
% 19.24/10.93  tff(c_34078, plain, (~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_32638, c_32885, c_34064])).
% 19.24/10.93  tff(c_34087, plain, (~v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_33802, c_34078])).
% 19.24/10.93  tff(c_34091, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_32638, c_27444, c_34087])).
% 19.24/10.93  tff(c_34092, plain, (u1_struct_0('#skF_1')='#skF_4'), inference(splitRight, [status(thm)], [c_32632])).
% 19.24/10.93  tff(c_34099, plain, (~v1_partfun1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34092, c_27647])).
% 19.24/10.93  tff(c_34106, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32253, c_34099])).
% 19.24/10.93  tff(c_34107, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_27627])).
% 19.24/10.93  tff(c_34606, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_32272, c_34107])).
% 19.24/10.93  tff(c_30592, plain, (![C_2127, B_2128]: (v1_funct_2(C_2127, k1_xboole_0, B_2128) | k1_relset_1(k1_xboole_0, B_2128, C_2127)!=k1_xboole_0 | ~m1_subset_1(C_2127, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_44])).
% 19.24/10.93  tff(c_30598, plain, (![B_2128]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_2128) | k1_relset_1(k1_xboole_0, B_2128, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_30592])).
% 19.24/10.93  tff(c_30602, plain, (![B_2128]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_2128))), inference(demodulation, [status(thm), theory('equality')], [c_30584, c_30598])).
% 19.24/10.93  tff(c_32244, plain, (![B_2128]: (v1_funct_2('#skF_4', '#skF_4', B_2128))), inference(demodulation, [status(thm), theory('equality')], [c_32208, c_32208, c_30602])).
% 19.24/10.93  tff(c_34424, plain, (![D_2419, A_2420, B_2421]: (v5_pre_topc(D_2419, g1_pre_topc(u1_struct_0(A_2420), u1_pre_topc(A_2420)), B_2421) | ~v5_pre_topc(D_2419, A_2420, B_2421) | ~m1_subset_1(D_2419, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2420), u1_pre_topc(A_2420))), u1_struct_0(B_2421)))) | ~v1_funct_2(D_2419, u1_struct_0(g1_pre_topc(u1_struct_0(A_2420), u1_pre_topc(A_2420))), u1_struct_0(B_2421)) | ~m1_subset_1(D_2419, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2420), u1_struct_0(B_2421)))) | ~v1_funct_2(D_2419, u1_struct_0(A_2420), u1_struct_0(B_2421)) | ~v1_funct_1(D_2419) | ~l1_pre_topc(B_2421) | ~v2_pre_topc(B_2421) | ~l1_pre_topc(A_2420) | ~v2_pre_topc(A_2420))), inference(cnfTransformation, [status(thm)], [f_158])).
% 19.24/10.93  tff(c_35230, plain, (![A_2492, A_2493, B_2494]: (v5_pre_topc(A_2492, g1_pre_topc(u1_struct_0(A_2493), u1_pre_topc(A_2493)), B_2494) | ~v5_pre_topc(A_2492, A_2493, B_2494) | ~v1_funct_2(A_2492, u1_struct_0(g1_pre_topc(u1_struct_0(A_2493), u1_pre_topc(A_2493))), u1_struct_0(B_2494)) | ~m1_subset_1(A_2492, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2493), u1_struct_0(B_2494)))) | ~v1_funct_2(A_2492, u1_struct_0(A_2493), u1_struct_0(B_2494)) | ~v1_funct_1(A_2492) | ~l1_pre_topc(B_2494) | ~v2_pre_topc(B_2494) | ~l1_pre_topc(A_2493) | ~v2_pre_topc(A_2493) | ~r1_tarski(A_2492, k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2493), u1_pre_topc(A_2493))), u1_struct_0(B_2494))))), inference(resolution, [status(thm)], [c_18, c_34424])).
% 19.24/10.93  tff(c_35575, plain, (![A_2516, B_2517]: (v5_pre_topc(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2516), u1_pre_topc(A_2516))), u1_struct_0(B_2517)), g1_pre_topc(u1_struct_0(A_2516), u1_pre_topc(A_2516)), B_2517) | ~v5_pre_topc(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2516), u1_pre_topc(A_2516))), u1_struct_0(B_2517)), A_2516, B_2517) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2516), u1_pre_topc(A_2516))), u1_struct_0(B_2517)), u1_struct_0(g1_pre_topc(u1_struct_0(A_2516), u1_pre_topc(A_2516))), u1_struct_0(B_2517)) | ~m1_subset_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2516), u1_pre_topc(A_2516))), u1_struct_0(B_2517)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2516), u1_struct_0(B_2517)))) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2516), u1_pre_topc(A_2516))), u1_struct_0(B_2517)), u1_struct_0(A_2516), u1_struct_0(B_2517)) | ~v1_funct_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2516), u1_pre_topc(A_2516))), u1_struct_0(B_2517))) | ~l1_pre_topc(B_2517) | ~v2_pre_topc(B_2517) | ~l1_pre_topc(A_2516) | ~v2_pre_topc(A_2516))), inference(resolution, [status(thm)], [c_6, c_35230])).
% 19.24/10.93  tff(c_35587, plain, (![B_2517]: (v5_pre_topc(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_2517)), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_2517) | ~v5_pre_topc(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_2517)), '#skF_1', B_2517) | ~v1_funct_2(k2_zfmisc_1('#skF_4', u1_struct_0(B_2517)), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_2517)) | ~m1_subset_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_2517)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_2517)))) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_2517)), u1_struct_0('#skF_1'), u1_struct_0(B_2517)) | ~v1_funct_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_2517))) | ~l1_pre_topc(B_2517) | ~v2_pre_topc(B_2517) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_34606, c_35575])).
% 19.24/10.93  tff(c_35617, plain, (![B_2517]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_2517) | ~v5_pre_topc('#skF_4', '#skF_1', B_2517) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0(B_2517)) | ~l1_pre_topc(B_2517) | ~v2_pre_topc(B_2517))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_80, c_32270, c_34606, c_32270, c_34606, c_32269, c_32270, c_34606, c_32244, c_32270, c_34606, c_32270, c_34606, c_32270, c_34606, c_35587])).
% 19.24/10.93  tff(c_34447, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_34444, c_27470])).
% 19.24/10.93  tff(c_474, plain, (![A_132]: (r1_tarski(u1_pre_topc(A_132), k1_zfmisc_1(u1_struct_0(A_132))) | ~l1_pre_topc(A_132))), inference(resolution, [status(thm)], [c_466, c_16])).
% 19.24/10.93  tff(c_34662, plain, (r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), k1_zfmisc_1('#skF_4')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_34606, c_474])).
% 19.24/10.93  tff(c_35266, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_34662])).
% 19.24/10.93  tff(c_35269, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_473, c_35266])).
% 19.24/10.93  tff(c_35273, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_35269])).
% 19.24/10.93  tff(c_35275, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_34662])).
% 19.24/10.93  tff(c_34656, plain, (v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_34606, c_62])).
% 19.24/10.93  tff(c_35564, plain, (v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_35275, c_34656])).
% 19.24/10.93  tff(c_35565, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_35564])).
% 19.24/10.93  tff(c_35568, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_35565])).
% 19.24/10.93  tff(c_35572, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_35568])).
% 19.24/10.93  tff(c_35574, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_35564])).
% 19.24/10.93  tff(c_34139, plain, (![D_2396, A_2397, B_2398]: (v5_pre_topc(D_2396, A_2397, g1_pre_topc(u1_struct_0(B_2398), u1_pre_topc(B_2398))) | ~v5_pre_topc(D_2396, A_2397, B_2398) | ~m1_subset_1(D_2396, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2397), u1_struct_0(g1_pre_topc(u1_struct_0(B_2398), u1_pre_topc(B_2398)))))) | ~v1_funct_2(D_2396, u1_struct_0(A_2397), u1_struct_0(g1_pre_topc(u1_struct_0(B_2398), u1_pre_topc(B_2398)))) | ~m1_subset_1(D_2396, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2397), u1_struct_0(B_2398)))) | ~v1_funct_2(D_2396, u1_struct_0(A_2397), u1_struct_0(B_2398)) | ~v1_funct_1(D_2396) | ~l1_pre_topc(B_2398) | ~v2_pre_topc(B_2398) | ~l1_pre_topc(A_2397) | ~v2_pre_topc(A_2397))), inference(cnfTransformation, [status(thm)], [f_187])).
% 19.24/10.93  tff(c_35048, plain, (![A_2478, A_2479, B_2480]: (v5_pre_topc(A_2478, A_2479, g1_pre_topc(u1_struct_0(B_2480), u1_pre_topc(B_2480))) | ~v5_pre_topc(A_2478, A_2479, B_2480) | ~v1_funct_2(A_2478, u1_struct_0(A_2479), u1_struct_0(g1_pre_topc(u1_struct_0(B_2480), u1_pre_topc(B_2480)))) | ~m1_subset_1(A_2478, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2479), u1_struct_0(B_2480)))) | ~v1_funct_2(A_2478, u1_struct_0(A_2479), u1_struct_0(B_2480)) | ~v1_funct_1(A_2478) | ~l1_pre_topc(B_2480) | ~v2_pre_topc(B_2480) | ~l1_pre_topc(A_2479) | ~v2_pre_topc(A_2479) | ~r1_tarski(A_2478, k2_zfmisc_1(u1_struct_0(A_2479), u1_struct_0(g1_pre_topc(u1_struct_0(B_2480), u1_pre_topc(B_2480))))))), inference(resolution, [status(thm)], [c_18, c_34139])).
% 19.24/10.93  tff(c_35657, plain, (![A_2520, B_2521]: (v5_pre_topc(k2_zfmisc_1(u1_struct_0(A_2520), u1_struct_0(g1_pre_topc(u1_struct_0(B_2521), u1_pre_topc(B_2521)))), A_2520, g1_pre_topc(u1_struct_0(B_2521), u1_pre_topc(B_2521))) | ~v5_pre_topc(k2_zfmisc_1(u1_struct_0(A_2520), u1_struct_0(g1_pre_topc(u1_struct_0(B_2521), u1_pre_topc(B_2521)))), A_2520, B_2521) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(A_2520), u1_struct_0(g1_pre_topc(u1_struct_0(B_2521), u1_pre_topc(B_2521)))), u1_struct_0(A_2520), u1_struct_0(g1_pre_topc(u1_struct_0(B_2521), u1_pre_topc(B_2521)))) | ~m1_subset_1(k2_zfmisc_1(u1_struct_0(A_2520), u1_struct_0(g1_pre_topc(u1_struct_0(B_2521), u1_pre_topc(B_2521)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2520), u1_struct_0(B_2521)))) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(A_2520), u1_struct_0(g1_pre_topc(u1_struct_0(B_2521), u1_pre_topc(B_2521)))), u1_struct_0(A_2520), u1_struct_0(B_2521)) | ~v1_funct_1(k2_zfmisc_1(u1_struct_0(A_2520), u1_struct_0(g1_pre_topc(u1_struct_0(B_2521), u1_pre_topc(B_2521))))) | ~l1_pre_topc(B_2521) | ~v2_pre_topc(B_2521) | ~l1_pre_topc(A_2520) | ~v2_pre_topc(A_2520))), inference(resolution, [status(thm)], [c_6, c_35048])).
% 19.24/10.93  tff(c_35675, plain, (![B_2521]: (v5_pre_topc(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0(B_2521), u1_pre_topc(B_2521)))), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0(B_2521), u1_pre_topc(B_2521))) | ~v5_pre_topc(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0(B_2521), u1_pre_topc(B_2521)))), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_2521) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0(B_2521), u1_pre_topc(B_2521)))), '#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(B_2521), u1_pre_topc(B_2521)))) | ~m1_subset_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0(B_2521), u1_pre_topc(B_2521)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_2521)))) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0(B_2521), u1_pre_topc(B_2521)))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_2521)) | ~v1_funct_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0(B_2521), u1_pre_topc(B_2521))))) | ~l1_pre_topc(B_2521) | ~v2_pre_topc(B_2521) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_34606, c_35657])).
% 19.24/10.93  tff(c_35751, plain, (![B_2524]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0(B_2524), u1_pre_topc(B_2524))) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_2524) | ~l1_pre_topc(B_2524) | ~v2_pre_topc(B_2524))), inference(demodulation, [status(thm), theory('equality')], [c_35574, c_35275, c_80, c_32270, c_34606, c_32244, c_32270, c_34606, c_34606, c_32269, c_32270, c_34606, c_34606, c_32244, c_32270, c_34606, c_32270, c_34606, c_32270, c_34606, c_35675])).
% 19.24/10.93  tff(c_35760, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_34444, c_35751])).
% 19.24/10.93  tff(c_35765, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_35760])).
% 19.24/10.93  tff(c_35766, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_34447, c_35765])).
% 19.24/10.93  tff(c_35789, plain, (~v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_35617, c_35766])).
% 19.24/10.93  tff(c_35793, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_34448, c_34444, c_27444, c_35789])).
% 19.24/10.93  tff(c_35794, plain, (u1_struct_0('#skF_1')='#skF_4'), inference(splitRight, [status(thm)], [c_34443])).
% 19.24/10.93  tff(c_35801, plain, (~v1_partfun1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_35794, c_27647])).
% 19.24/10.93  tff(c_35808, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32253, c_35801])).
% 19.24/10.93  tff(c_35809, plain, (u1_struct_0('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_27630])).
% 19.24/10.93  tff(c_35821, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_35809, c_78])).
% 19.24/10.93  tff(c_35819, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))))), inference(demodulation, [status(thm), theory('equality')], [c_35809, c_76])).
% 19.24/10.93  tff(c_35999, plain, (![A_2528, B_2529, C_2530]: (k1_relset_1(A_2528, B_2529, C_2530)=k1_relat_1(C_2530) | ~m1_subset_1(C_2530, k1_zfmisc_1(k2_zfmisc_1(A_2528, B_2529))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 19.24/10.93  tff(c_36021, plain, (k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_35819, c_35999])).
% 19.24/10.93  tff(c_45967, plain, (![B_3097, A_3098, C_3099]: (k1_xboole_0=B_3097 | k1_relset_1(A_3098, B_3097, C_3099)=A_3098 | ~v1_funct_2(C_3099, A_3098, B_3097) | ~m1_subset_1(C_3099, k1_zfmisc_1(k2_zfmisc_1(A_3098, B_3097))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 19.24/10.93  tff(c_45973, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0 | k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')=u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(resolution, [status(thm)], [c_35819, c_45967])).
% 19.24/10.93  tff(c_45993, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0 | u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_35821, c_36021, c_45973])).
% 19.24/10.93  tff(c_46217, plain, (u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_45993])).
% 19.24/10.93  tff(c_35816, plain, (r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))))), inference(demodulation, [status(thm), theory('equality')], [c_35809, c_176])).
% 19.24/10.93  tff(c_46220, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))))), inference(demodulation, [status(thm), theory('equality')], [c_46217, c_35816])).
% 19.24/10.93  tff(c_35820, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_35809, c_103])).
% 19.24/10.93  tff(c_35818, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_35809, c_107])).
% 19.24/10.93  tff(c_46223, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_46217, c_35821])).
% 19.24/10.93  tff(c_35817, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_35809, c_193])).
% 19.24/10.93  tff(c_46194, plain, (![D_3128, A_3129, B_3130]: (v5_pre_topc(D_3128, g1_pre_topc(u1_struct_0(A_3129), u1_pre_topc(A_3129)), B_3130) | ~v5_pre_topc(D_3128, A_3129, B_3130) | ~m1_subset_1(D_3128, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_3129), u1_pre_topc(A_3129))), u1_struct_0(B_3130)))) | ~v1_funct_2(D_3128, u1_struct_0(g1_pre_topc(u1_struct_0(A_3129), u1_pre_topc(A_3129))), u1_struct_0(B_3130)) | ~m1_subset_1(D_3128, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3129), u1_struct_0(B_3130)))) | ~v1_funct_2(D_3128, u1_struct_0(A_3129), u1_struct_0(B_3130)) | ~v1_funct_1(D_3128) | ~l1_pre_topc(B_3130) | ~v2_pre_topc(B_3130) | ~l1_pre_topc(A_3129) | ~v2_pre_topc(A_3129))), inference(cnfTransformation, [status(thm)], [f_158])).
% 19.24/10.93  tff(c_47506, plain, (![A_3215, A_3216, B_3217]: (v5_pre_topc(A_3215, g1_pre_topc(u1_struct_0(A_3216), u1_pre_topc(A_3216)), B_3217) | ~v5_pre_topc(A_3215, A_3216, B_3217) | ~v1_funct_2(A_3215, u1_struct_0(g1_pre_topc(u1_struct_0(A_3216), u1_pre_topc(A_3216))), u1_struct_0(B_3217)) | ~m1_subset_1(A_3215, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3216), u1_struct_0(B_3217)))) | ~v1_funct_2(A_3215, u1_struct_0(A_3216), u1_struct_0(B_3217)) | ~v1_funct_1(A_3215) | ~l1_pre_topc(B_3217) | ~v2_pre_topc(B_3217) | ~l1_pre_topc(A_3216) | ~v2_pre_topc(A_3216) | ~r1_tarski(A_3215, k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_3216), u1_pre_topc(A_3216))), u1_struct_0(B_3217))))), inference(resolution, [status(thm)], [c_18, c_46194])).
% 19.24/10.93  tff(c_47515, plain, (![A_3215, B_3217]: (v5_pre_topc(A_3215, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_3217) | ~v5_pre_topc(A_3215, '#skF_1', B_3217) | ~v1_funct_2(A_3215, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_3217)) | ~m1_subset_1(A_3215, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_3217)))) | ~v1_funct_2(A_3215, u1_struct_0('#skF_1'), u1_struct_0(B_3217)) | ~v1_funct_1(A_3215) | ~l1_pre_topc(B_3217) | ~v2_pre_topc(B_3217) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(A_3215, k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(B_3217))))), inference(superposition, [status(thm), theory('equality')], [c_35809, c_47506])).
% 19.24/10.93  tff(c_47780, plain, (![A_3229, B_3230]: (v5_pre_topc(A_3229, g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), B_3230) | ~v5_pre_topc(A_3229, '#skF_1', B_3230) | ~m1_subset_1(A_3229, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_3230)))) | ~v1_funct_2(A_3229, k1_relat_1('#skF_4'), u1_struct_0(B_3230)) | ~v1_funct_1(A_3229) | ~l1_pre_topc(B_3230) | ~v2_pre_topc(B_3230) | ~r1_tarski(A_3229, k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_3230))))), inference(demodulation, [status(thm), theory('equality')], [c_46217, c_94, c_92, c_35809, c_35809, c_46217, c_35809, c_35809, c_47515])).
% 19.24/10.93  tff(c_47789, plain, (v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), '#skF_2') | ~v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~r1_tarski('#skF_4', k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_35818, c_47780])).
% 19.24/10.93  tff(c_47809, plain, (v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_35817, c_90, c_88, c_80, c_35820, c_27444, c_47789])).
% 19.24/10.93  tff(c_35825, plain, (v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_35809, c_62])).
% 19.24/10.93  tff(c_35841, plain, (v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_35825])).
% 19.24/10.93  tff(c_35834, plain, (l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_35809, c_473])).
% 19.24/10.93  tff(c_35847, plain, (l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_35834])).
% 19.24/10.93  tff(c_46345, plain, (![D_3131, A_3132, B_3133]: (v5_pre_topc(D_3131, A_3132, g1_pre_topc(u1_struct_0(B_3133), u1_pre_topc(B_3133))) | ~v5_pre_topc(D_3131, A_3132, B_3133) | ~m1_subset_1(D_3131, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3132), u1_struct_0(g1_pre_topc(u1_struct_0(B_3133), u1_pre_topc(B_3133)))))) | ~v1_funct_2(D_3131, u1_struct_0(A_3132), u1_struct_0(g1_pre_topc(u1_struct_0(B_3133), u1_pre_topc(B_3133)))) | ~m1_subset_1(D_3131, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3132), u1_struct_0(B_3133)))) | ~v1_funct_2(D_3131, u1_struct_0(A_3132), u1_struct_0(B_3133)) | ~v1_funct_1(D_3131) | ~l1_pre_topc(B_3133) | ~v2_pre_topc(B_3133) | ~l1_pre_topc(A_3132) | ~v2_pre_topc(A_3132))), inference(cnfTransformation, [status(thm)], [f_187])).
% 19.24/10.93  tff(c_47822, plain, (![A_3231, A_3232, B_3233]: (v5_pre_topc(A_3231, A_3232, g1_pre_topc(u1_struct_0(B_3233), u1_pre_topc(B_3233))) | ~v5_pre_topc(A_3231, A_3232, B_3233) | ~v1_funct_2(A_3231, u1_struct_0(A_3232), u1_struct_0(g1_pre_topc(u1_struct_0(B_3233), u1_pre_topc(B_3233)))) | ~m1_subset_1(A_3231, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3232), u1_struct_0(B_3233)))) | ~v1_funct_2(A_3231, u1_struct_0(A_3232), u1_struct_0(B_3233)) | ~v1_funct_1(A_3231) | ~l1_pre_topc(B_3233) | ~v2_pre_topc(B_3233) | ~l1_pre_topc(A_3232) | ~v2_pre_topc(A_3232) | ~r1_tarski(A_3231, k2_zfmisc_1(u1_struct_0(A_3232), u1_struct_0(g1_pre_topc(u1_struct_0(B_3233), u1_pre_topc(B_3233))))))), inference(resolution, [status(thm)], [c_18, c_46345])).
% 19.24/10.93  tff(c_47825, plain, (![A_3231, B_3233]: (v5_pre_topc(A_3231, g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0(B_3233), u1_pre_topc(B_3233))) | ~v5_pre_topc(A_3231, g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), B_3233) | ~v1_funct_2(A_3231, u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0(B_3233), u1_pre_topc(B_3233)))) | ~m1_subset_1(A_3231, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(B_3233)))) | ~v1_funct_2(A_3231, u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(B_3233)) | ~v1_funct_1(A_3231) | ~l1_pre_topc(B_3233) | ~v2_pre_topc(B_3233) | ~l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))) | ~r1_tarski(A_3231, k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0(B_3233), u1_pre_topc(B_3233))))))), inference(superposition, [status(thm), theory('equality')], [c_46217, c_47822])).
% 19.24/10.93  tff(c_48788, plain, (![A_3274, B_3275]: (v5_pre_topc(A_3274, g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0(B_3275), u1_pre_topc(B_3275))) | ~v5_pre_topc(A_3274, g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), B_3275) | ~v1_funct_2(A_3274, k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0(B_3275), u1_pre_topc(B_3275)))) | ~m1_subset_1(A_3274, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_3275)))) | ~v1_funct_2(A_3274, k1_relat_1('#skF_4'), u1_struct_0(B_3275)) | ~v1_funct_1(A_3274) | ~l1_pre_topc(B_3275) | ~v2_pre_topc(B_3275) | ~r1_tarski(A_3274, k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0(B_3275), u1_pre_topc(B_3275))))))), inference(demodulation, [status(thm), theory('equality')], [c_35841, c_35847, c_46217, c_46217, c_46217, c_47825])).
% 19.24/10.93  tff(c_35813, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_35809, c_27470])).
% 19.24/10.93  tff(c_48813, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), '#skF_2') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~r1_tarski('#skF_4', k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))))), inference(resolution, [status(thm)], [c_48788, c_35813])).
% 19.24/10.93  tff(c_48837, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46220, c_90, c_88, c_80, c_35820, c_35818, c_46223, c_47809, c_48813])).
% 19.24/10.93  tff(c_48838, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0), inference(splitRight, [status(thm)], [c_45993])).
% 19.24/10.93  tff(c_48842, plain, (r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_48838, c_35816])).
% 19.24/10.93  tff(c_48847, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_48842])).
% 19.24/10.93  tff(c_48914, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_48847, c_168])).
% 19.24/10.93  tff(c_48961, plain, (![B_4]: (k2_zfmisc_1('#skF_4', B_4)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48914, c_48914, c_12])).
% 19.24/10.93  tff(c_48963, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_48914, c_48914, c_24])).
% 19.24/10.93  tff(c_46137, plain, (k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'))='#skF_4' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_35809, c_35809, c_196])).
% 19.24/10.93  tff(c_46138, plain, (~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2')), '#skF_4')), inference(splitLeft, [status(thm)], [c_46137])).
% 19.24/10.93  tff(c_49012, plain, (~r1_tarski(k2_zfmisc_1('#skF_4', u1_struct_0('#skF_2')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48963, c_46138])).
% 19.24/10.93  tff(c_49629, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_48961, c_49012])).
% 19.24/10.93  tff(c_49630, plain, (k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'))='#skF_4'), inference(splitRight, [status(thm)], [c_46137])).
% 19.24/10.93  tff(c_49682, plain, (u1_struct_0('#skF_2')=k1_xboole_0 | k1_relat_1('#skF_4')=k1_xboole_0 | k1_xboole_0!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_49630, c_8])).
% 19.24/10.93  tff(c_49796, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_49682])).
% 19.24/10.93  tff(c_49633, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_49630, c_35818])).
% 19.24/10.93  tff(c_52098, plain, (u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_45993])).
% 19.24/10.93  tff(c_51999, plain, (![D_3447, A_3448, B_3449]: (v5_pre_topc(D_3447, g1_pre_topc(u1_struct_0(A_3448), u1_pre_topc(A_3448)), B_3449) | ~v5_pre_topc(D_3447, A_3448, B_3449) | ~m1_subset_1(D_3447, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_3448), u1_pre_topc(A_3448))), u1_struct_0(B_3449)))) | ~v1_funct_2(D_3447, u1_struct_0(g1_pre_topc(u1_struct_0(A_3448), u1_pre_topc(A_3448))), u1_struct_0(B_3449)) | ~m1_subset_1(D_3447, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3448), u1_struct_0(B_3449)))) | ~v1_funct_2(D_3447, u1_struct_0(A_3448), u1_struct_0(B_3449)) | ~v1_funct_1(D_3447) | ~l1_pre_topc(B_3449) | ~v2_pre_topc(B_3449) | ~l1_pre_topc(A_3448) | ~v2_pre_topc(A_3448))), inference(cnfTransformation, [status(thm)], [f_158])).
% 19.24/10.93  tff(c_53908, plain, (![A_3519, A_3520, B_3521]: (v5_pre_topc(A_3519, g1_pre_topc(u1_struct_0(A_3520), u1_pre_topc(A_3520)), B_3521) | ~v5_pre_topc(A_3519, A_3520, B_3521) | ~v1_funct_2(A_3519, u1_struct_0(g1_pre_topc(u1_struct_0(A_3520), u1_pre_topc(A_3520))), u1_struct_0(B_3521)) | ~m1_subset_1(A_3519, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3520), u1_struct_0(B_3521)))) | ~v1_funct_2(A_3519, u1_struct_0(A_3520), u1_struct_0(B_3521)) | ~v1_funct_1(A_3519) | ~l1_pre_topc(B_3521) | ~v2_pre_topc(B_3521) | ~l1_pre_topc(A_3520) | ~v2_pre_topc(A_3520) | ~r1_tarski(A_3519, k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_3520), u1_pre_topc(A_3520))), u1_struct_0(B_3521))))), inference(resolution, [status(thm)], [c_18, c_51999])).
% 19.24/10.93  tff(c_53917, plain, (![A_3519, B_3521]: (v5_pre_topc(A_3519, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_3521) | ~v5_pre_topc(A_3519, '#skF_1', B_3521) | ~v1_funct_2(A_3519, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_3521)) | ~m1_subset_1(A_3519, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_3521)))) | ~v1_funct_2(A_3519, u1_struct_0('#skF_1'), u1_struct_0(B_3521)) | ~v1_funct_1(A_3519) | ~l1_pre_topc(B_3521) | ~v2_pre_topc(B_3521) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(A_3519, k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(B_3521))))), inference(superposition, [status(thm), theory('equality')], [c_35809, c_53908])).
% 19.24/10.93  tff(c_54797, plain, (![A_3566, B_3567]: (v5_pre_topc(A_3566, g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), B_3567) | ~v5_pre_topc(A_3566, '#skF_1', B_3567) | ~m1_subset_1(A_3566, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_3567)))) | ~v1_funct_2(A_3566, k1_relat_1('#skF_4'), u1_struct_0(B_3567)) | ~v1_funct_1(A_3566) | ~l1_pre_topc(B_3567) | ~v2_pre_topc(B_3567) | ~r1_tarski(A_3566, k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_3567))))), inference(demodulation, [status(thm), theory('equality')], [c_52098, c_94, c_92, c_35809, c_35809, c_52098, c_35809, c_35809, c_53917])).
% 19.24/10.93  tff(c_54806, plain, (![A_3566]: (v5_pre_topc(A_3566, g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), '#skF_2') | ~v5_pre_topc(A_3566, '#skF_1', '#skF_2') | ~m1_subset_1(A_3566, k1_zfmisc_1('#skF_4')) | ~v1_funct_2(A_3566, k1_relat_1('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(A_3566) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~r1_tarski(A_3566, k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_49630, c_54797])).
% 19.24/10.93  tff(c_54878, plain, (![A_3570]: (v5_pre_topc(A_3570, g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), '#skF_2') | ~v5_pre_topc(A_3570, '#skF_1', '#skF_2') | ~m1_subset_1(A_3570, k1_zfmisc_1('#skF_4')) | ~v1_funct_2(A_3570, k1_relat_1('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(A_3570) | ~r1_tarski(A_3570, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_49630, c_90, c_88, c_54806])).
% 19.24/10.93  tff(c_49722, plain, (![D_3321, A_3322, B_3323]: (v5_pre_topc(D_3321, A_3322, g1_pre_topc(u1_struct_0(B_3323), u1_pre_topc(B_3323))) | ~v5_pre_topc(D_3321, A_3322, B_3323) | ~m1_subset_1(D_3321, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3322), u1_struct_0(g1_pre_topc(u1_struct_0(B_3323), u1_pre_topc(B_3323)))))) | ~v1_funct_2(D_3321, u1_struct_0(A_3322), u1_struct_0(g1_pre_topc(u1_struct_0(B_3323), u1_pre_topc(B_3323)))) | ~m1_subset_1(D_3321, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3322), u1_struct_0(B_3323)))) | ~v1_funct_2(D_3321, u1_struct_0(A_3322), u1_struct_0(B_3323)) | ~v1_funct_1(D_3321) | ~l1_pre_topc(B_3323) | ~v2_pre_topc(B_3323) | ~l1_pre_topc(A_3322) | ~v2_pre_topc(A_3322))), inference(cnfTransformation, [status(thm)], [f_187])).
% 19.24/10.93  tff(c_49725, plain, (v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_35819, c_49722])).
% 19.24/10.93  tff(c_49742, plain, (v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_35841, c_35847, c_90, c_88, c_80, c_35821, c_49725])).
% 19.24/10.93  tff(c_49743, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_35813, c_49742])).
% 19.24/10.93  tff(c_53169, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_35820, c_52098, c_49633, c_49630, c_52098, c_49743])).
% 19.24/10.93  tff(c_54891, plain, (~v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4')) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_54878, c_53169])).
% 19.24/10.93  tff(c_54902, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_80, c_35820, c_49633, c_27444, c_54891])).
% 19.24/10.93  tff(c_54903, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0), inference(splitRight, [status(thm)], [c_45993])).
% 19.24/10.93  tff(c_50034, plain, (u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_45993])).
% 19.24/10.93  tff(c_49967, plain, (![D_3340, A_3341, B_3342]: (v5_pre_topc(D_3340, g1_pre_topc(u1_struct_0(A_3341), u1_pre_topc(A_3341)), B_3342) | ~v5_pre_topc(D_3340, A_3341, B_3342) | ~m1_subset_1(D_3340, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_3341), u1_pre_topc(A_3341))), u1_struct_0(B_3342)))) | ~v1_funct_2(D_3340, u1_struct_0(g1_pre_topc(u1_struct_0(A_3341), u1_pre_topc(A_3341))), u1_struct_0(B_3342)) | ~m1_subset_1(D_3340, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3341), u1_struct_0(B_3342)))) | ~v1_funct_2(D_3340, u1_struct_0(A_3341), u1_struct_0(B_3342)) | ~v1_funct_1(D_3340) | ~l1_pre_topc(B_3342) | ~v2_pre_topc(B_3342) | ~l1_pre_topc(A_3341) | ~v2_pre_topc(A_3341))), inference(cnfTransformation, [status(thm)], [f_158])).
% 19.24/10.93  tff(c_51616, plain, (![A_3426, A_3427, B_3428]: (v5_pre_topc(A_3426, g1_pre_topc(u1_struct_0(A_3427), u1_pre_topc(A_3427)), B_3428) | ~v5_pre_topc(A_3426, A_3427, B_3428) | ~v1_funct_2(A_3426, u1_struct_0(g1_pre_topc(u1_struct_0(A_3427), u1_pre_topc(A_3427))), u1_struct_0(B_3428)) | ~m1_subset_1(A_3426, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3427), u1_struct_0(B_3428)))) | ~v1_funct_2(A_3426, u1_struct_0(A_3427), u1_struct_0(B_3428)) | ~v1_funct_1(A_3426) | ~l1_pre_topc(B_3428) | ~v2_pre_topc(B_3428) | ~l1_pre_topc(A_3427) | ~v2_pre_topc(A_3427) | ~r1_tarski(A_3426, k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_3427), u1_pre_topc(A_3427))), u1_struct_0(B_3428))))), inference(resolution, [status(thm)], [c_18, c_49967])).
% 19.24/10.93  tff(c_51625, plain, (![A_3426, B_3428]: (v5_pre_topc(A_3426, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_3428) | ~v5_pre_topc(A_3426, '#skF_1', B_3428) | ~v1_funct_2(A_3426, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_3428)) | ~m1_subset_1(A_3426, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_3428)))) | ~v1_funct_2(A_3426, u1_struct_0('#skF_1'), u1_struct_0(B_3428)) | ~v1_funct_1(A_3426) | ~l1_pre_topc(B_3428) | ~v2_pre_topc(B_3428) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(A_3426, k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(B_3428))))), inference(superposition, [status(thm), theory('equality')], [c_35809, c_51616])).
% 19.24/10.93  tff(c_51827, plain, (![A_3438, B_3439]: (v5_pre_topc(A_3438, g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), B_3439) | ~v5_pre_topc(A_3438, '#skF_1', B_3439) | ~m1_subset_1(A_3438, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_3439)))) | ~v1_funct_2(A_3438, k1_relat_1('#skF_4'), u1_struct_0(B_3439)) | ~v1_funct_1(A_3438) | ~l1_pre_topc(B_3439) | ~v2_pre_topc(B_3439) | ~r1_tarski(A_3438, k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_3439))))), inference(demodulation, [status(thm), theory('equality')], [c_50034, c_94, c_92, c_35809, c_35809, c_50034, c_35809, c_35809, c_51625])).
% 19.24/10.93  tff(c_51836, plain, (![A_3438]: (v5_pre_topc(A_3438, g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), '#skF_2') | ~v5_pre_topc(A_3438, '#skF_1', '#skF_2') | ~m1_subset_1(A_3438, k1_zfmisc_1('#skF_4')) | ~v1_funct_2(A_3438, k1_relat_1('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(A_3438) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~r1_tarski(A_3438, k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_49630, c_51827])).
% 19.24/10.93  tff(c_51922, plain, (![A_3442]: (v5_pre_topc(A_3442, g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), '#skF_2') | ~v5_pre_topc(A_3442, '#skF_1', '#skF_2') | ~m1_subset_1(A_3442, k1_zfmisc_1('#skF_4')) | ~v1_funct_2(A_3442, k1_relat_1('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(A_3442) | ~r1_tarski(A_3442, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_49630, c_90, c_88, c_51836])).
% 19.24/10.93  tff(c_51149, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_35820, c_50034, c_49633, c_49630, c_50034, c_49743])).
% 19.24/10.93  tff(c_51929, plain, (~v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4')) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_51922, c_51149])).
% 19.24/10.93  tff(c_51936, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_80, c_35820, c_49633, c_27444, c_51929])).
% 19.24/10.93  tff(c_51937, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0), inference(splitRight, [status(thm)], [c_45993])).
% 19.24/10.93  tff(c_49918, plain, (k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))='#skF_4' | ~r1_tarski(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_35809, c_35809, c_246])).
% 19.24/10.93  tff(c_49919, plain, (~r1_tarski(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), '#skF_4')), inference(splitLeft, [status(thm)], [c_49918])).
% 19.24/10.93  tff(c_51941, plain, (~r1_tarski(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), k1_xboole_0), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_51937, c_49919])).
% 19.24/10.93  tff(c_51950, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_161, c_10, c_51941])).
% 19.24/10.93  tff(c_51951, plain, (k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))='#skF_4'), inference(splitRight, [status(thm)], [c_49918])).
% 19.24/10.93  tff(c_54905, plain, (k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), k1_xboole_0)='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_54903, c_51951])).
% 19.24/10.93  tff(c_55036, plain, (k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_54905, c_10])).
% 19.24/10.93  tff(c_55049, plain, $false, inference(negUnitSimplification, [status(thm)], [c_49796, c_55036])).
% 19.24/10.93  tff(c_55051, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_49682])).
% 19.24/10.93  tff(c_55095, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_55051, c_55051, c_24])).
% 19.24/10.93  tff(c_55172, plain, (~v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_55095, c_35813])).
% 19.24/10.93  tff(c_55093, plain, (![B_4]: (k2_zfmisc_1('#skF_4', B_4)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_55051, c_55051, c_12])).
% 19.24/10.93  tff(c_56892, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))='#skF_4' | u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_55095, c_55095, c_55051, c_45993])).
% 19.24/10.93  tff(c_56893, plain, (u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')))='#skF_4'), inference(splitLeft, [status(thm)], [c_56892])).
% 19.24/10.93  tff(c_55191, plain, (u1_struct_0('#skF_1')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_55095, c_35809])).
% 19.24/10.93  tff(c_36013, plain, (![A_2528, B_2529]: (k1_relset_1(A_2528, B_2529, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_35999])).
% 19.24/10.93  tff(c_36024, plain, (![A_2528, B_2529]: (k1_relset_1(A_2528, B_2529, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_36013])).
% 19.24/10.93  tff(c_36216, plain, (![C_2559, B_2560]: (v1_funct_2(C_2559, k1_xboole_0, B_2560) | k1_relset_1(k1_xboole_0, B_2560, C_2559)!=k1_xboole_0 | ~m1_subset_1(C_2559, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_44])).
% 19.24/10.93  tff(c_36222, plain, (![B_2560]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_2560) | k1_relset_1(k1_xboole_0, B_2560, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_36216])).
% 19.24/10.93  tff(c_36226, plain, (![B_2560]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_2560))), inference(demodulation, [status(thm), theory('equality')], [c_36024, c_36222])).
% 19.24/10.93  tff(c_55062, plain, (![B_2560]: (v1_funct_2('#skF_4', '#skF_4', B_2560))), inference(demodulation, [status(thm), theory('equality')], [c_55051, c_55051, c_36226])).
% 19.24/10.93  tff(c_55092, plain, (![A_5]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_55051, c_14])).
% 19.24/10.93  tff(c_55150, plain, (![D_3572, A_3573, B_3574]: (v5_pre_topc(D_3572, g1_pre_topc(u1_struct_0(A_3573), u1_pre_topc(A_3573)), B_3574) | ~v5_pre_topc(D_3572, A_3573, B_3574) | ~m1_subset_1(D_3572, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_3573), u1_pre_topc(A_3573))), u1_struct_0(B_3574)))) | ~v1_funct_2(D_3572, u1_struct_0(g1_pre_topc(u1_struct_0(A_3573), u1_pre_topc(A_3573))), u1_struct_0(B_3574)) | ~m1_subset_1(D_3572, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3573), u1_struct_0(B_3574)))) | ~v1_funct_2(D_3572, u1_struct_0(A_3573), u1_struct_0(B_3574)) | ~v1_funct_1(D_3572) | ~l1_pre_topc(B_3574) | ~v2_pre_topc(B_3574) | ~l1_pre_topc(A_3573) | ~v2_pre_topc(A_3573))), inference(cnfTransformation, [status(thm)], [f_158])).
% 19.24/10.93  tff(c_57180, plain, (![A_3766, A_3767, B_3768]: (v5_pre_topc(A_3766, g1_pre_topc(u1_struct_0(A_3767), u1_pre_topc(A_3767)), B_3768) | ~v5_pre_topc(A_3766, A_3767, B_3768) | ~v1_funct_2(A_3766, u1_struct_0(g1_pre_topc(u1_struct_0(A_3767), u1_pre_topc(A_3767))), u1_struct_0(B_3768)) | ~m1_subset_1(A_3766, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3767), u1_struct_0(B_3768)))) | ~v1_funct_2(A_3766, u1_struct_0(A_3767), u1_struct_0(B_3768)) | ~v1_funct_1(A_3766) | ~l1_pre_topc(B_3768) | ~v2_pre_topc(B_3768) | ~l1_pre_topc(A_3767) | ~v2_pre_topc(A_3767) | ~r1_tarski(A_3766, k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_3767), u1_pre_topc(A_3767))), u1_struct_0(B_3768))))), inference(resolution, [status(thm)], [c_18, c_55150])).
% 19.24/10.93  tff(c_57775, plain, (![A_3821, B_3822]: (v5_pre_topc(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_3821), u1_pre_topc(A_3821))), u1_struct_0(B_3822)), g1_pre_topc(u1_struct_0(A_3821), u1_pre_topc(A_3821)), B_3822) | ~v5_pre_topc(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_3821), u1_pre_topc(A_3821))), u1_struct_0(B_3822)), A_3821, B_3822) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_3821), u1_pre_topc(A_3821))), u1_struct_0(B_3822)), u1_struct_0(g1_pre_topc(u1_struct_0(A_3821), u1_pre_topc(A_3821))), u1_struct_0(B_3822)) | ~m1_subset_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_3821), u1_pre_topc(A_3821))), u1_struct_0(B_3822)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3821), u1_struct_0(B_3822)))) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_3821), u1_pre_topc(A_3821))), u1_struct_0(B_3822)), u1_struct_0(A_3821), u1_struct_0(B_3822)) | ~v1_funct_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_3821), u1_pre_topc(A_3821))), u1_struct_0(B_3822))) | ~l1_pre_topc(B_3822) | ~v2_pre_topc(B_3822) | ~l1_pre_topc(A_3821) | ~v2_pre_topc(A_3821))), inference(resolution, [status(thm)], [c_6, c_57180])).
% 19.24/10.93  tff(c_57796, plain, (![B_3822]: (v5_pre_topc(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_3822)), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_3822) | ~v5_pre_topc(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_3822)), '#skF_1', B_3822) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), u1_struct_0(B_3822)), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_3822)) | ~m1_subset_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_3822)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_3822)))) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_3822)), u1_struct_0('#skF_1'), u1_struct_0(B_3822)) | ~v1_funct_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_3822))) | ~l1_pre_topc(B_3822) | ~v2_pre_topc(B_3822) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_55191, c_57775])).
% 19.24/10.93  tff(c_57825, plain, (![B_3823]: (v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), B_3823) | ~v5_pre_topc('#skF_4', '#skF_1', B_3823) | ~l1_pre_topc(B_3823) | ~v2_pre_topc(B_3823))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_80, c_55093, c_56893, c_55191, c_55062, c_55093, c_56893, c_55191, c_55191, c_55092, c_55093, c_56893, c_55093, c_55191, c_55191, c_55062, c_56893, c_55093, c_56893, c_55191, c_55093, c_56893, c_55191, c_55093, c_56893, c_55191, c_55191, c_57796])).
% 19.24/10.93  tff(c_55186, plain, (v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_55095, c_35841])).
% 19.24/10.93  tff(c_55184, plain, (l1_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_55095, c_35847])).
% 19.24/10.93  tff(c_55190, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_55095, c_35821])).
% 19.24/10.93  tff(c_27534, plain, (![B_1892, A_1893]: (v1_funct_1(B_1892) | ~m1_subset_1(B_1892, k1_zfmisc_1(A_1893)) | ~v1_funct_1(A_1893) | ~v1_relat_1(A_1893))), inference(cnfTransformation, [status(thm)], [f_61])).
% 19.24/10.93  tff(c_27558, plain, (![A_5]: (v1_funct_1(k1_xboole_0) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(resolution, [status(thm)], [c_14, c_27534])).
% 19.24/10.93  tff(c_27560, plain, (![A_1894]: (~v1_funct_1(A_1894) | ~v1_relat_1(A_1894))), inference(splitLeft, [status(thm)], [c_27558])).
% 19.24/10.93  tff(c_27569, plain, (~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_216, c_27560])).
% 19.24/10.93  tff(c_27575, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_27569])).
% 19.24/10.93  tff(c_27576, plain, (v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_27558])).
% 19.24/10.93  tff(c_49739, plain, (![A_3322, B_3323]: (v5_pre_topc(k1_xboole_0, A_3322, g1_pre_topc(u1_struct_0(B_3323), u1_pre_topc(B_3323))) | ~v5_pre_topc(k1_xboole_0, A_3322, B_3323) | ~v1_funct_2(k1_xboole_0, u1_struct_0(A_3322), u1_struct_0(g1_pre_topc(u1_struct_0(B_3323), u1_pre_topc(B_3323)))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3322), u1_struct_0(B_3323)))) | ~v1_funct_2(k1_xboole_0, u1_struct_0(A_3322), u1_struct_0(B_3323)) | ~v1_funct_1(k1_xboole_0) | ~l1_pre_topc(B_3323) | ~v2_pre_topc(B_3323) | ~l1_pre_topc(A_3322) | ~v2_pre_topc(A_3322))), inference(resolution, [status(thm)], [c_14, c_49722])).
% 19.24/10.93  tff(c_49751, plain, (![A_3322, B_3323]: (v5_pre_topc(k1_xboole_0, A_3322, g1_pre_topc(u1_struct_0(B_3323), u1_pre_topc(B_3323))) | ~v5_pre_topc(k1_xboole_0, A_3322, B_3323) | ~v1_funct_2(k1_xboole_0, u1_struct_0(A_3322), u1_struct_0(g1_pre_topc(u1_struct_0(B_3323), u1_pre_topc(B_3323)))) | ~v1_funct_2(k1_xboole_0, u1_struct_0(A_3322), u1_struct_0(B_3323)) | ~l1_pre_topc(B_3323) | ~v2_pre_topc(B_3323) | ~l1_pre_topc(A_3322) | ~v2_pre_topc(A_3322))), inference(demodulation, [status(thm), theory('equality')], [c_27576, c_14, c_49739])).
% 19.24/10.93  tff(c_56920, plain, (![A_3741, B_3742]: (v5_pre_topc('#skF_4', A_3741, g1_pre_topc(u1_struct_0(B_3742), u1_pre_topc(B_3742))) | ~v5_pre_topc('#skF_4', A_3741, B_3742) | ~v1_funct_2('#skF_4', u1_struct_0(A_3741), u1_struct_0(g1_pre_topc(u1_struct_0(B_3742), u1_pre_topc(B_3742)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_3741), u1_struct_0(B_3742)) | ~l1_pre_topc(B_3742) | ~v2_pre_topc(B_3742) | ~l1_pre_topc(A_3741) | ~v2_pre_topc(A_3741))), inference(demodulation, [status(thm), theory('equality')], [c_55051, c_55051, c_55051, c_55051, c_49751])).
% 19.24/10.93  tff(c_56929, plain, (v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_55190, c_56920])).
% 19.24/10.93  tff(c_56936, plain, (v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_55186, c_55184, c_90, c_88, c_56929])).
% 19.24/10.93  tff(c_57755, plain, (v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_55062, c_56893, c_56936])).
% 19.24/10.93  tff(c_57756, plain, (~v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_55172, c_57755])).
% 19.24/10.93  tff(c_57828, plain, (~v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_57825, c_57756])).
% 19.24/10.93  tff(c_57838, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_27444, c_57828])).
% 19.24/10.93  tff(c_57839, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))='#skF_4'), inference(splitRight, [status(thm)], [c_56892])).
% 19.24/10.93  tff(c_57985, plain, (r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), k1_zfmisc_1('#skF_4')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_57839, c_474])).
% 19.24/10.93  tff(c_58642, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_57985])).
% 19.24/10.93  tff(c_58645, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_473, c_58642])).
% 19.24/10.93  tff(c_58649, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_58645])).
% 19.24/10.93  tff(c_58651, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_57985])).
% 19.24/10.93  tff(c_57979, plain, (v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_57839, c_62])).
% 19.24/10.93  tff(c_59029, plain, (v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_58651, c_57979])).
% 19.24/10.93  tff(c_59030, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_59029])).
% 19.24/10.93  tff(c_59033, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_62, c_59030])).
% 19.24/10.93  tff(c_59037, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_59033])).
% 19.24/10.93  tff(c_59039, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_59029])).
% 19.24/10.93  tff(c_57912, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_57839, c_55190])).
% 19.24/10.93  tff(c_57868, plain, (![A_3828, B_3829]: (v5_pre_topc('#skF_4', A_3828, g1_pre_topc(u1_struct_0(B_3829), u1_pre_topc(B_3829))) | ~v5_pre_topc('#skF_4', A_3828, B_3829) | ~v1_funct_2('#skF_4', u1_struct_0(A_3828), u1_struct_0(g1_pre_topc(u1_struct_0(B_3829), u1_pre_topc(B_3829)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_3828), u1_struct_0(B_3829)) | ~l1_pre_topc(B_3829) | ~v2_pre_topc(B_3829) | ~l1_pre_topc(A_3828) | ~v2_pre_topc(A_3828))), inference(demodulation, [status(thm), theory('equality')], [c_55051, c_55051, c_55051, c_55051, c_49751])).
% 19.24/10.93  tff(c_57871, plain, (![B_3829]: (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0(B_3829), u1_pre_topc(B_3829))) | ~v5_pre_topc('#skF_4', '#skF_1', B_3829) | ~v1_funct_2('#skF_4', '#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(B_3829), u1_pre_topc(B_3829)))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0(B_3829)) | ~l1_pre_topc(B_3829) | ~v2_pre_topc(B_3829) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_55191, c_57868])).
% 19.24/10.93  tff(c_57879, plain, (![B_3829]: (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0(B_3829), u1_pre_topc(B_3829))) | ~v5_pre_topc('#skF_4', '#skF_1', B_3829) | ~l1_pre_topc(B_3829) | ~v2_pre_topc(B_3829))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_55062, c_55191, c_55062, c_57871])).
% 19.24/10.93  tff(c_55292, plain, (![D_3577, A_3578, B_3579]: (v5_pre_topc(D_3577, A_3578, B_3579) | ~v5_pre_topc(D_3577, A_3578, g1_pre_topc(u1_struct_0(B_3579), u1_pre_topc(B_3579))) | ~m1_subset_1(D_3577, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3578), u1_struct_0(g1_pre_topc(u1_struct_0(B_3579), u1_pre_topc(B_3579)))))) | ~v1_funct_2(D_3577, u1_struct_0(A_3578), u1_struct_0(g1_pre_topc(u1_struct_0(B_3579), u1_pre_topc(B_3579)))) | ~m1_subset_1(D_3577, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3578), u1_struct_0(B_3579)))) | ~v1_funct_2(D_3577, u1_struct_0(A_3578), u1_struct_0(B_3579)) | ~v1_funct_1(D_3577) | ~l1_pre_topc(B_3579) | ~v2_pre_topc(B_3579) | ~l1_pre_topc(A_3578) | ~v2_pre_topc(A_3578))), inference(cnfTransformation, [status(thm)], [f_187])).
% 19.24/10.93  tff(c_58213, plain, (![A_3860, A_3861, B_3862]: (v5_pre_topc(A_3860, A_3861, B_3862) | ~v5_pre_topc(A_3860, A_3861, g1_pre_topc(u1_struct_0(B_3862), u1_pre_topc(B_3862))) | ~v1_funct_2(A_3860, u1_struct_0(A_3861), u1_struct_0(g1_pre_topc(u1_struct_0(B_3862), u1_pre_topc(B_3862)))) | ~m1_subset_1(A_3860, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3861), u1_struct_0(B_3862)))) | ~v1_funct_2(A_3860, u1_struct_0(A_3861), u1_struct_0(B_3862)) | ~v1_funct_1(A_3860) | ~l1_pre_topc(B_3862) | ~v2_pre_topc(B_3862) | ~l1_pre_topc(A_3861) | ~v2_pre_topc(A_3861) | ~r1_tarski(A_3860, k2_zfmisc_1(u1_struct_0(A_3861), u1_struct_0(g1_pre_topc(u1_struct_0(B_3862), u1_pre_topc(B_3862))))))), inference(resolution, [status(thm)], [c_18, c_55292])).
% 19.24/10.93  tff(c_58786, plain, (![A_3906, B_3907]: (v5_pre_topc(k2_zfmisc_1(u1_struct_0(A_3906), u1_struct_0(g1_pre_topc(u1_struct_0(B_3907), u1_pre_topc(B_3907)))), A_3906, B_3907) | ~v5_pre_topc(k2_zfmisc_1(u1_struct_0(A_3906), u1_struct_0(g1_pre_topc(u1_struct_0(B_3907), u1_pre_topc(B_3907)))), A_3906, g1_pre_topc(u1_struct_0(B_3907), u1_pre_topc(B_3907))) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(A_3906), u1_struct_0(g1_pre_topc(u1_struct_0(B_3907), u1_pre_topc(B_3907)))), u1_struct_0(A_3906), u1_struct_0(g1_pre_topc(u1_struct_0(B_3907), u1_pre_topc(B_3907)))) | ~m1_subset_1(k2_zfmisc_1(u1_struct_0(A_3906), u1_struct_0(g1_pre_topc(u1_struct_0(B_3907), u1_pre_topc(B_3907)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3906), u1_struct_0(B_3907)))) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(A_3906), u1_struct_0(g1_pre_topc(u1_struct_0(B_3907), u1_pre_topc(B_3907)))), u1_struct_0(A_3906), u1_struct_0(B_3907)) | ~v1_funct_1(k2_zfmisc_1(u1_struct_0(A_3906), u1_struct_0(g1_pre_topc(u1_struct_0(B_3907), u1_pre_topc(B_3907))))) | ~l1_pre_topc(B_3907) | ~v2_pre_topc(B_3907) | ~l1_pre_topc(A_3906) | ~v2_pre_topc(A_3906))), inference(resolution, [status(thm)], [c_6, c_58213])).
% 19.24/10.93  tff(c_58813, plain, (![B_3907]: (v5_pre_topc(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(g1_pre_topc(u1_struct_0(B_3907), u1_pre_topc(B_3907)))), '#skF_1', B_3907) | ~v5_pre_topc(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(g1_pre_topc(u1_struct_0(B_3907), u1_pre_topc(B_3907)))), '#skF_1', g1_pre_topc(u1_struct_0(B_3907), u1_pre_topc(B_3907))) | ~v1_funct_2(k2_zfmisc_1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(B_3907), u1_pre_topc(B_3907)))), u1_struct_0('#skF_1'), u1_struct_0(g1_pre_topc(u1_struct_0(B_3907), u1_pre_topc(B_3907)))) | ~m1_subset_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(g1_pre_topc(u1_struct_0(B_3907), u1_pre_topc(B_3907)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_3907)))) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(g1_pre_topc(u1_struct_0(B_3907), u1_pre_topc(B_3907)))), u1_struct_0('#skF_1'), u1_struct_0(B_3907)) | ~v1_funct_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(g1_pre_topc(u1_struct_0(B_3907), u1_pre_topc(B_3907))))) | ~l1_pre_topc(B_3907) | ~v2_pre_topc(B_3907) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_55191, c_58786])).
% 19.24/10.93  tff(c_58845, plain, (![B_3908]: (v5_pre_topc('#skF_4', '#skF_1', B_3908) | ~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0(B_3908), u1_pre_topc(B_3908))) | ~l1_pre_topc(B_3908) | ~v2_pre_topc(B_3908))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_80, c_55093, c_55191, c_55062, c_55191, c_55093, c_55191, c_55092, c_55093, c_55191, c_55062, c_55191, c_55093, c_55093, c_55191, c_55093, c_55191, c_58813])).
% 19.24/10.93  tff(c_58851, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_57839, c_58845])).
% 19.24/10.93  tff(c_58857, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_58651, c_58851])).
% 19.24/10.93  tff(c_59108, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))))), inference(demodulation, [status(thm), theory('equality')], [c_59039, c_58857])).
% 19.24/10.93  tff(c_59109, plain, (~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))))), inference(splitLeft, [status(thm)], [c_59108])).
% 19.24/10.93  tff(c_58774, plain, (![B_3905]: (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0(B_3905), u1_pre_topc(B_3905))) | ~v5_pre_topc('#skF_4', '#skF_1', B_3905) | ~l1_pre_topc(B_3905) | ~v2_pre_topc(B_3905))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_55062, c_55191, c_55062, c_57871])).
% 19.24/10.93  tff(c_58777, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_57839, c_58774])).
% 19.24/10.93  tff(c_58782, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_58651, c_58777])).
% 19.24/10.93  tff(c_59111, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_59039, c_58782])).
% 19.24/10.93  tff(c_59112, plain, (~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_59109, c_59111])).
% 19.24/10.93  tff(c_59115, plain, (~v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_57879, c_59112])).
% 19.24/10.93  tff(c_59119, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_27444, c_59115])).
% 19.24/10.93  tff(c_59120, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_59108])).
% 19.24/10.93  tff(c_55153, plain, (![D_3572, B_3574]: (v5_pre_topc(D_3572, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_3574) | ~v5_pre_topc(D_3572, '#skF_1', B_3574) | ~m1_subset_1(D_3572, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(B_3574)))) | ~v1_funct_2(D_3572, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_3574)) | ~m1_subset_1(D_3572, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_3574)))) | ~v1_funct_2(D_3572, u1_struct_0('#skF_1'), u1_struct_0(B_3574)) | ~v1_funct_1(D_3572) | ~l1_pre_topc(B_3574) | ~v2_pre_topc(B_3574) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_35809, c_55150])).
% 19.24/10.93  tff(c_55162, plain, (![D_3572, B_3574]: (v5_pre_topc(D_3572, g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), B_3574) | ~v5_pre_topc(D_3572, '#skF_1', B_3574) | ~m1_subset_1(D_3572, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(B_3574)))) | ~v1_funct_2(D_3572, u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(B_3574)) | ~m1_subset_1(D_3572, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_3574)))) | ~v1_funct_2(D_3572, k1_relat_1('#skF_4'), u1_struct_0(B_3574)) | ~v1_funct_1(D_3572) | ~l1_pre_topc(B_3574) | ~v2_pre_topc(B_3574))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_35809, c_35809, c_35809, c_35809, c_55153])).
% 19.24/10.93  tff(c_59284, plain, (![D_3934, B_3935]: (v5_pre_topc(D_3934, g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), B_3935) | ~v5_pre_topc(D_3934, '#skF_1', B_3935) | ~m1_subset_1(D_3934, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), u1_struct_0(B_3935)))) | ~v1_funct_2(D_3934, u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), u1_struct_0(B_3935)) | ~m1_subset_1(D_3934, k1_zfmisc_1('#skF_4')) | ~v1_funct_2(D_3934, '#skF_4', u1_struct_0(B_3935)) | ~v1_funct_1(D_3934) | ~l1_pre_topc(B_3935) | ~v2_pre_topc(B_3935))), inference(demodulation, [status(thm), theory('equality')], [c_55095, c_55093, c_55095, c_55095, c_55095, c_55095, c_55162])).
% 19.24/10.93  tff(c_59291, plain, (![B_3935]: (v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), B_3935) | ~v5_pre_topc('#skF_4', '#skF_1', B_3935) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), u1_struct_0(B_3935)) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4')) | ~v1_funct_2('#skF_4', '#skF_4', u1_struct_0(B_3935)) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(B_3935) | ~v2_pre_topc(B_3935))), inference(resolution, [status(thm)], [c_55092, c_59284])).
% 19.24/10.93  tff(c_59372, plain, (![B_3936]: (v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), B_3936) | ~v5_pre_topc('#skF_4', '#skF_1', B_3936) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), u1_struct_0(B_3936)) | ~l1_pre_topc(B_3936) | ~v2_pre_topc(B_3936))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_55062, c_55092, c_59291])).
% 19.24/10.93  tff(c_59381, plain, (v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), '#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_57839, c_59372])).
% 19.24/10.93  tff(c_59388, plain, (v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_59039, c_58651, c_57912, c_59120, c_59381])).
% 19.24/10.93  tff(c_59390, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55172, c_59388])).
% 19.24/10.93  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.24/10.93  
% 19.24/10.93  Inference rules
% 19.24/10.93  ----------------------
% 19.24/10.93  #Ref     : 0
% 19.24/10.93  #Sup     : 10948
% 19.24/10.93  #Fact    : 0
% 19.24/10.93  #Define  : 0
% 19.24/10.93  #Split   : 229
% 19.24/10.93  #Chain   : 0
% 19.24/10.93  #Close   : 0
% 19.24/10.93  
% 19.24/10.93  Ordering : KBO
% 19.24/10.93  
% 19.24/10.93  Simplification rules
% 19.24/10.93  ----------------------
% 19.24/10.93  #Subsume      : 3212
% 19.24/10.93  #Demod        : 33997
% 19.24/10.93  #Tautology    : 3956
% 19.24/10.93  #SimpNegUnit  : 409
% 19.24/10.93  #BackRed      : 1791
% 19.24/10.94  
% 19.24/10.94  #Partial instantiations: 0
% 19.24/10.94  #Strategies tried      : 1
% 19.24/10.94  
% 19.24/10.94  Timing (in seconds)
% 19.24/10.94  ----------------------
% 19.24/10.94  Preprocessing        : 0.40
% 19.24/10.94  Parsing              : 0.21
% 19.24/10.94  CNF conversion       : 0.03
% 19.24/10.94  Main loop            : 9.55
% 19.24/10.94  Inferencing          : 2.53
% 19.24/10.94  Reduction            : 4.40
% 19.24/10.94  Demodulation         : 3.52
% 19.24/10.94  BG Simplification    : 0.20
% 19.24/10.94  Subsumption          : 1.92
% 19.24/10.94  Abstraction          : 0.32
% 19.65/10.94  MUC search           : 0.00
% 19.65/10.94  Cooper               : 0.00
% 19.65/10.94  Total                : 10.20
% 19.65/10.94  Index Insertion      : 0.00
% 19.65/10.94  Index Deletion       : 0.00
% 19.65/10.94  Index Matching       : 0.00
% 19.65/10.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
