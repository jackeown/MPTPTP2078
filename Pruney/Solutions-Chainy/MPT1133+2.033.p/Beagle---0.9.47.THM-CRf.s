%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:16 EST 2020

% Result     : Theorem 15.99s
% Output     : CNFRefutation 17.05s
% Verified   : 
% Statistics : Number of formulae       : 1302 (235034 expanded)
%              Number of leaves         :   40 (76033 expanded)
%              Depth                    :   31
%              Number of atoms          : 3867 (1023518 expanded)
%              Number of equality atoms :  424 (226864 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_pre_topc > v1_relat_1 > v1_pre_topc > v1_funct_1 > l1_pre_topc > k1_relset_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_193,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_pre_topc)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_75,axiom,(
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

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_134,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_pre_topc)).

tff(f_105,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

tff(f_97,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_93,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v1_pre_topc(g1_pre_topc(A,B))
        & l1_pre_topc(g1_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

tff(f_163,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_pre_topc)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( k1_relset_1(A,B,C) = A
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_funct_2)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_58,plain,(
    '#skF_3' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_91,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_66])).

tff(c_106,plain,(
    ! [C_72,A_73,B_74] :
      ( v1_relat_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_110,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_91,c_106])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_136,plain,(
    ! [C_84,A_85,B_86] :
      ( v4_relat_1(C_84,A_85)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_143,plain,(
    v4_relat_1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(resolution,[status(thm)],[c_60,c_136])).

tff(c_10,plain,(
    ! [B_4,A_3] :
      ( r1_tarski(k1_relat_1(B_4),A_3)
      | ~ v4_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_78,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_76,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_27251,plain,(
    ! [D_1407,B_1408,C_1409,A_1410] :
      ( m1_subset_1(D_1407,k1_zfmisc_1(k2_zfmisc_1(B_1408,C_1409)))
      | ~ r1_tarski(k1_relat_1(D_1407),B_1408)
      | ~ m1_subset_1(D_1407,k1_zfmisc_1(k2_zfmisc_1(A_1410,C_1409))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_27258,plain,(
    ! [B_1411] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_1411,u1_struct_0('#skF_2'))))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_1411) ) ),
    inference(resolution,[status(thm)],[c_91,c_27251])).

tff(c_30,plain,(
    ! [B_19,C_20] :
      ( k1_relset_1(k1_xboole_0,B_19,C_20) = k1_xboole_0
      | ~ v1_funct_2(C_20,k1_xboole_0,B_19)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_27282,plain,
    ( k1_relset_1(k1_xboole_0,u1_struct_0('#skF_2'),'#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_4',k1_xboole_0,u1_struct_0('#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_27258,c_30])).

tff(c_27410,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_27282])).

tff(c_27413,plain,
    ( ~ v4_relat_1('#skF_4',k1_xboole_0)
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_27410])).

tff(c_27416,plain,(
    ~ v4_relat_1('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_27413])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_68,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_87,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_68])).

tff(c_27221,plain,(
    ! [A_1396,B_1397,C_1398] :
      ( k1_relset_1(A_1396,B_1397,C_1398) = k1_relat_1(C_1398)
      | ~ m1_subset_1(C_1398,k1_zfmisc_1(k2_zfmisc_1(A_1396,B_1397))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_27229,plain,(
    k1_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_91,c_27221])).

tff(c_27418,plain,(
    ! [B_1420,A_1421,C_1422] :
      ( k1_xboole_0 = B_1420
      | k1_relset_1(A_1421,B_1420,C_1422) = A_1421
      | ~ v1_funct_2(C_1422,A_1421,B_1420)
      | ~ m1_subset_1(C_1422,k1_zfmisc_1(k2_zfmisc_1(A_1421,B_1420))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_27430,plain,
    ( u1_struct_0('#skF_2') = k1_xboole_0
    | k1_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4') = u1_struct_0('#skF_1')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_91,c_27418])).

tff(c_27438,plain,
    ( u1_struct_0('#skF_2') = k1_xboole_0
    | u1_struct_0('#skF_1') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_27229,c_27430])).

tff(c_27439,plain,(
    u1_struct_0('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_27438])).

tff(c_86,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_88,plain,
    ( v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_86])).

tff(c_162,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_80,plain,
    ( ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_90,plain,
    ( ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_80])).

tff(c_194,plain,(
    ~ v5_pre_topc('#skF_4','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_90])).

tff(c_144,plain,(
    v4_relat_1('#skF_4',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_91,c_136])).

tff(c_195,plain,(
    ! [D_106,B_107,C_108,A_109] :
      ( m1_subset_1(D_106,k1_zfmisc_1(k2_zfmisc_1(B_107,C_108)))
      | ~ r1_tarski(k1_relat_1(D_106),B_107)
      | ~ m1_subset_1(D_106,k1_zfmisc_1(k2_zfmisc_1(A_109,C_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_202,plain,(
    ! [B_110] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_110,u1_struct_0('#skF_2'))))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_110) ) ),
    inference(resolution,[status(thm)],[c_91,c_195])).

tff(c_227,plain,
    ( k1_relset_1(k1_xboole_0,u1_struct_0('#skF_2'),'#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_4',k1_xboole_0,u1_struct_0('#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_202,c_30])).

tff(c_369,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_227])).

tff(c_372,plain,
    ( ~ v4_relat_1('#skF_4',k1_xboole_0)
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_369])).

tff(c_375,plain,(
    ~ v4_relat_1('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_372])).

tff(c_165,plain,(
    ! [A_95,B_96,C_97] :
      ( k1_relset_1(A_95,B_96,C_97) = k1_relat_1(C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_173,plain,(
    k1_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_91,c_165])).

tff(c_413,plain,(
    ! [B_125,A_126,C_127] :
      ( k1_xboole_0 = B_125
      | k1_relset_1(A_126,B_125,C_127) = A_126
      | ~ v1_funct_2(C_127,A_126,B_125)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_126,B_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_425,plain,
    ( u1_struct_0('#skF_2') = k1_xboole_0
    | k1_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4') = u1_struct_0('#skF_1')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_91,c_413])).

tff(c_433,plain,
    ( u1_struct_0('#skF_2') = k1_xboole_0
    | u1_struct_0('#skF_1') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_173,c_425])).

tff(c_3860,plain,(
    u1_struct_0('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_433])).

tff(c_3869,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3860,c_87])).

tff(c_74,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_72,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_435,plain,(
    u1_struct_0('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_433])).

tff(c_444,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_87])).

tff(c_442,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_91])).

tff(c_62,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_172,plain,(
    k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_165])).

tff(c_422,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0
    | k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') = u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(resolution,[status(thm)],[c_60,c_413])).

tff(c_430,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_172,c_422])).

tff(c_434,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_430])).

tff(c_540,plain,(
    u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_434])).

tff(c_1690,plain,(
    ! [D_200,A_201,B_202] :
      ( v5_pre_topc(D_200,A_201,B_202)
      | ~ v5_pre_topc(D_200,g1_pre_topc(u1_struct_0(A_201),u1_pre_topc(A_201)),B_202)
      | ~ m1_subset_1(D_200,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_201),u1_pre_topc(A_201))),u1_struct_0(B_202))))
      | ~ v1_funct_2(D_200,u1_struct_0(g1_pre_topc(u1_struct_0(A_201),u1_pre_topc(A_201))),u1_struct_0(B_202))
      | ~ m1_subset_1(D_200,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_201),u1_struct_0(B_202))))
      | ~ v1_funct_2(D_200,u1_struct_0(A_201),u1_struct_0(B_202))
      | ~ v1_funct_1(D_200)
      | ~ l1_pre_topc(B_202)
      | ~ v2_pre_topc(B_202)
      | ~ l1_pre_topc(A_201)
      | ~ v2_pre_topc(A_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1699,plain,(
    ! [D_200,B_202] :
      ( v5_pre_topc(D_200,'#skF_1',B_202)
      | ~ v5_pre_topc(D_200,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_202)
      | ~ m1_subset_1(D_200,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(B_202))))
      | ~ v1_funct_2(D_200,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_202))
      | ~ m1_subset_1(D_200,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_202))))
      | ~ v1_funct_2(D_200,u1_struct_0('#skF_1'),u1_struct_0(B_202))
      | ~ v1_funct_1(D_200)
      | ~ l1_pre_topc(B_202)
      | ~ v2_pre_topc(B_202)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_435,c_1690])).

tff(c_2476,plain,(
    ! [D_242,B_243] :
      ( v5_pre_topc(D_242,'#skF_1',B_243)
      | ~ v5_pre_topc(D_242,g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),B_243)
      | ~ m1_subset_1(D_242,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_243))))
      | ~ v1_funct_2(D_242,k1_relat_1('#skF_4'),u1_struct_0(B_243))
      | ~ v1_funct_1(D_242)
      | ~ l1_pre_topc(B_243)
      | ~ v2_pre_topc(B_243) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_435,c_435,c_540,c_435,c_540,c_435,c_1699])).

tff(c_2485,plain,
    ( v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_442,c_2476])).

tff(c_2504,plain,
    ( v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_64,c_444,c_2485])).

tff(c_2505,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_194,c_2504])).

tff(c_46,plain,(
    ! [A_27] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(A_27),u1_pre_topc(A_27)))
      | ~ l1_pre_topc(A_27)
      | ~ v2_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_450,plain,
    ( v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_435,c_46])).

tff(c_463,plain,(
    v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_450])).

tff(c_116,plain,(
    ! [A_79] :
      ( m1_subset_1(u1_pre_topc(A_79),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_79))))
      | ~ l1_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_40,plain,(
    ! [A_24,B_25] :
      ( l1_pre_topc(g1_pre_topc(A_24,B_25))
      | ~ m1_subset_1(B_25,k1_zfmisc_1(k1_zfmisc_1(A_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_120,plain,(
    ! [A_79] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_79),u1_pre_topc(A_79)))
      | ~ l1_pre_topc(A_79) ) ),
    inference(resolution,[status(thm)],[c_116,c_40])).

tff(c_456,plain,
    ( l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_435,c_120])).

tff(c_467,plain,(
    l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_456])).

tff(c_443,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_62])).

tff(c_542,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_540,c_443])).

tff(c_437,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_162])).

tff(c_200,plain,(
    ! [B_107] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_107,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_107) ) ),
    inference(resolution,[status(thm)],[c_60,c_195])).

tff(c_471,plain,(
    ! [D_128,A_129,B_130] :
      ( v5_pre_topc(D_128,A_129,B_130)
      | ~ v5_pre_topc(D_128,A_129,g1_pre_topc(u1_struct_0(B_130),u1_pre_topc(B_130)))
      | ~ m1_subset_1(D_128,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_129),u1_struct_0(g1_pre_topc(u1_struct_0(B_130),u1_pre_topc(B_130))))))
      | ~ v1_funct_2(D_128,u1_struct_0(A_129),u1_struct_0(g1_pre_topc(u1_struct_0(B_130),u1_pre_topc(B_130))))
      | ~ m1_subset_1(D_128,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_129),u1_struct_0(B_130))))
      | ~ v1_funct_2(D_128,u1_struct_0(A_129),u1_struct_0(B_130))
      | ~ v1_funct_1(D_128)
      | ~ l1_pre_topc(B_130)
      | ~ v2_pre_topc(B_130)
      | ~ l1_pre_topc(A_129)
      | ~ v2_pre_topc(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_481,plain,(
    ! [A_129] :
      ( v5_pre_topc('#skF_4',A_129,'#skF_2')
      | ~ v5_pre_topc('#skF_4',A_129,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_129),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_129),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_129),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_129)
      | ~ v2_pre_topc(A_129)
      | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(A_129)) ) ),
    inference(resolution,[status(thm)],[c_200,c_471])).

tff(c_2551,plain,(
    ! [A_247] :
      ( v5_pre_topc('#skF_4',A_247,'#skF_2')
      | ~ v5_pre_topc('#skF_4',A_247,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_247),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_247),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_247),u1_struct_0('#skF_2'))
      | ~ l1_pre_topc(A_247)
      | ~ v2_pre_topc(A_247)
      | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(A_247)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_64,c_481])).

tff(c_2557,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2'))
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))
    | ~ v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))
    | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_540,c_2551])).

tff(c_2563,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_540,c_463,c_467,c_444,c_540,c_442,c_540,c_542,c_437,c_2557])).

tff(c_2565,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2505,c_2563])).

tff(c_2566,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_433])).

tff(c_2583,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2566,c_87])).

tff(c_2581,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2566,c_91])).

tff(c_24,plain,(
    ! [C_20,A_18] :
      ( k1_xboole_0 = C_20
      | ~ v1_funct_2(C_20,A_18,k1_xboole_0)
      | k1_xboole_0 = A_18
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2642,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),k1_xboole_0)
    | u1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2581,c_24])).

tff(c_2668,plain,
    ( k1_xboole_0 = '#skF_4'
    | u1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2583,c_2642])).

tff(c_2676,plain,(
    u1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2668])).

tff(c_2682,plain,(
    v4_relat_1('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2676,c_144])).

tff(c_2684,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_375,c_2682])).

tff(c_2685,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2668])).

tff(c_2693,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2685,c_2583])).

tff(c_2687,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),'#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2685,c_2581])).

tff(c_201,plain,(
    ! [B_107] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_107,u1_struct_0('#skF_2'))))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_107) ) ),
    inference(resolution,[status(thm)],[c_91,c_195])).

tff(c_2575,plain,(
    ! [B_107] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_107,k1_xboole_0)))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2566,c_201])).

tff(c_2969,plain,(
    ! [B_107] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_107,'#skF_4')))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2685,c_2575])).

tff(c_22,plain,(
    ! [A_18] :
      ( v1_funct_2(k1_xboole_0,A_18,k1_xboole_0)
      | k1_xboole_0 = A_18
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_18,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_3090,plain,(
    ! [A_264] :
      ( v1_funct_2('#skF_4',A_264,'#skF_4')
      | A_264 = '#skF_4'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_264,'#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2685,c_2685,c_2685,c_2685,c_2685,c_22])).

tff(c_3101,plain,(
    ! [B_265] :
      ( v1_funct_2('#skF_4',B_265,'#skF_4')
      | B_265 = '#skF_4'
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_265) ) ),
    inference(resolution,[status(thm)],[c_2969,c_3090])).

tff(c_3113,plain,
    ( v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_4')
    | k1_relat_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6,c_3101])).

tff(c_3114,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3113])).

tff(c_2698,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2685,c_369])).

tff(c_3126,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3114,c_2698])).

tff(c_3132,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3126])).

tff(c_3133,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_3113])).

tff(c_2926,plain,
    ( l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_434,c_120])).

tff(c_3215,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2926])).

tff(c_3218,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_120,c_3215])).

tff(c_3222,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_3218])).

tff(c_3224,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_2926])).

tff(c_2920,plain,
    ( v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_434,c_46])).

tff(c_3588,plain,
    ( v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3224,c_2920])).

tff(c_3589,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_3588])).

tff(c_3592,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_3589])).

tff(c_3596,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_3592])).

tff(c_3598,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_3588])).

tff(c_2582,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2566,c_62])).

tff(c_2688,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2685,c_2582])).

tff(c_2949,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_434,c_2688])).

tff(c_2576,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2566,c_162])).

tff(c_3014,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2685,c_2576])).

tff(c_2571,plain,(
    ! [B_107] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_107,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2'))))))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2566,c_200])).

tff(c_3047,plain,(
    ! [B_107] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_107,u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2685,c_2571])).

tff(c_2608,plain,(
    ! [D_248,A_249,B_250] :
      ( v5_pre_topc(D_248,A_249,B_250)
      | ~ v5_pre_topc(D_248,A_249,g1_pre_topc(u1_struct_0(B_250),u1_pre_topc(B_250)))
      | ~ m1_subset_1(D_248,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_249),u1_struct_0(g1_pre_topc(u1_struct_0(B_250),u1_pre_topc(B_250))))))
      | ~ v1_funct_2(D_248,u1_struct_0(A_249),u1_struct_0(g1_pre_topc(u1_struct_0(B_250),u1_pre_topc(B_250))))
      | ~ m1_subset_1(D_248,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_249),u1_struct_0(B_250))))
      | ~ v1_funct_2(D_248,u1_struct_0(A_249),u1_struct_0(B_250))
      | ~ v1_funct_1(D_248)
      | ~ l1_pre_topc(B_250)
      | ~ v2_pre_topc(B_250)
      | ~ l1_pre_topc(A_249)
      | ~ v2_pre_topc(A_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_2614,plain,(
    ! [D_248,A_249] :
      ( v5_pre_topc(D_248,A_249,'#skF_2')
      | ~ v5_pre_topc(D_248,A_249,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ m1_subset_1(D_248,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_249),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2'))))))
      | ~ v1_funct_2(D_248,u1_struct_0(A_249),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1(D_248,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_249),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_248,u1_struct_0(A_249),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_248)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_249)
      | ~ v2_pre_topc(A_249) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2566,c_2608])).

tff(c_2618,plain,(
    ! [D_248,A_249] :
      ( v5_pre_topc(D_248,A_249,'#skF_2')
      | ~ v5_pre_topc(D_248,A_249,g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2')))
      | ~ m1_subset_1(D_248,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_249),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2'))))))
      | ~ v1_funct_2(D_248,u1_struct_0(A_249),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1(D_248,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_249),k1_xboole_0)))
      | ~ v1_funct_2(D_248,u1_struct_0(A_249),k1_xboole_0)
      | ~ v1_funct_1(D_248)
      | ~ l1_pre_topc(A_249)
      | ~ v2_pre_topc(A_249) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_2566,c_2566,c_2566,c_2566,c_2614])).

tff(c_3731,plain,(
    ! [D_314,A_315] :
      ( v5_pre_topc(D_314,A_315,'#skF_2')
      | ~ v5_pre_topc(D_314,A_315,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ m1_subset_1(D_314,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_315),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))))
      | ~ v1_funct_2(D_314,u1_struct_0(A_315),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1(D_314,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_315),'#skF_4')))
      | ~ v1_funct_2(D_314,u1_struct_0(A_315),'#skF_4')
      | ~ v1_funct_1(D_314)
      | ~ l1_pre_topc(A_315)
      | ~ v2_pre_topc(A_315) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2685,c_2685,c_2685,c_2685,c_2685,c_2618])).

tff(c_3735,plain,(
    ! [A_315] :
      ( v5_pre_topc('#skF_4',A_315,'#skF_2')
      | ~ v5_pre_topc('#skF_4',A_315,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_315),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_315),'#skF_4')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_315),'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(A_315)
      | ~ v2_pre_topc(A_315)
      | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(A_315)) ) ),
    inference(resolution,[status(thm)],[c_3047,c_3731])).

tff(c_3766,plain,(
    ! [A_318] :
      ( v5_pre_topc('#skF_4',A_318,'#skF_2')
      | ~ v5_pre_topc('#skF_4',A_318,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_318),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_318),'#skF_4')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_318),'#skF_4')
      | ~ l1_pre_topc(A_318)
      | ~ v2_pre_topc(A_318)
      | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(A_318)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_3735])).

tff(c_3772,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_434,c_3766])).

tff(c_3778,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_434,c_3598,c_3224,c_3133,c_434,c_434,c_2949,c_3014,c_3772])).

tff(c_3781,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_3778])).

tff(c_3784,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_2969,c_3781])).

tff(c_3788,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3784])).

tff(c_3790,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_3778])).

tff(c_3789,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_3778])).

tff(c_2695,plain,(
    u1_struct_0('#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2685,c_2566])).

tff(c_50,plain,(
    ! [D_42,A_28,B_36] :
      ( v5_pre_topc(D_42,A_28,B_36)
      | ~ v5_pre_topc(D_42,g1_pre_topc(u1_struct_0(A_28),u1_pre_topc(A_28)),B_36)
      | ~ m1_subset_1(D_42,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_28),u1_pre_topc(A_28))),u1_struct_0(B_36))))
      | ~ v1_funct_2(D_42,u1_struct_0(g1_pre_topc(u1_struct_0(A_28),u1_pre_topc(A_28))),u1_struct_0(B_36))
      | ~ m1_subset_1(D_42,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_28),u1_struct_0(B_36))))
      | ~ v1_funct_2(D_42,u1_struct_0(A_28),u1_struct_0(B_36))
      | ~ v1_funct_1(D_42)
      | ~ l1_pre_topc(B_36)
      | ~ v2_pre_topc(B_36)
      | ~ l1_pre_topc(A_28)
      | ~ v2_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_2905,plain,(
    ! [D_42,B_36] :
      ( v5_pre_topc(D_42,'#skF_1',B_36)
      | ~ v5_pre_topc(D_42,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_36)
      | ~ m1_subset_1(D_42,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_36))))
      | ~ v1_funct_2(D_42,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_36))
      | ~ m1_subset_1(D_42,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_36))))
      | ~ v1_funct_2(D_42,u1_struct_0('#skF_1'),u1_struct_0(B_36))
      | ~ v1_funct_1(D_42)
      | ~ l1_pre_topc(B_36)
      | ~ v2_pre_topc(B_36)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_434,c_50])).

tff(c_3600,plain,(
    ! [D_302,B_303] :
      ( v5_pre_topc(D_302,'#skF_1',B_303)
      | ~ v5_pre_topc(D_302,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_303)
      | ~ m1_subset_1(D_302,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_303))))
      | ~ v1_funct_2(D_302,k1_relat_1('#skF_4'),u1_struct_0(B_303))
      | ~ m1_subset_1(D_302,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_303))))
      | ~ v1_funct_2(D_302,u1_struct_0('#skF_1'),u1_struct_0(B_303))
      | ~ v1_funct_1(D_302)
      | ~ l1_pre_topc(B_303)
      | ~ v2_pre_topc(B_303) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_434,c_2905])).

tff(c_3610,plain,(
    ! [D_302] :
      ( v5_pre_topc(D_302,'#skF_1','#skF_2')
      | ~ v5_pre_topc(D_302,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
      | ~ m1_subset_1(D_302,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_302,k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(D_302,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),'#skF_4')))
      | ~ v1_funct_2(D_302,u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_302)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2695,c_3600])).

tff(c_3617,plain,(
    ! [D_302] :
      ( v5_pre_topc(D_302,'#skF_1','#skF_2')
      | ~ v5_pre_topc(D_302,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
      | ~ m1_subset_1(D_302,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_4')))
      | ~ v1_funct_2(D_302,k1_relat_1('#skF_4'),'#skF_4')
      | ~ m1_subset_1(D_302,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),'#skF_4')))
      | ~ v1_funct_2(D_302,u1_struct_0('#skF_1'),'#skF_4')
      | ~ v1_funct_1(D_302) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_2695,c_2695,c_2695,c_3610])).

tff(c_3852,plain,
    ( v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_4')))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),'#skF_4')))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_3789,c_3617])).

tff(c_3855,plain,(
    v5_pre_topc('#skF_4','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2693,c_2687,c_3133,c_3790,c_3852])).

tff(c_3857,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_194,c_3855])).

tff(c_3858,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_430])).

tff(c_3868,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3860,c_62])).

tff(c_3921,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3858,c_3868])).

tff(c_3866,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3860,c_60])).

tff(c_4082,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3858,c_3866])).

tff(c_4096,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),k1_xboole_0)
    | u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4082,c_24])).

tff(c_4122,plain,
    ( k1_xboole_0 = '#skF_4'
    | u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3921,c_4096])).

tff(c_4130,plain,(
    u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_4122])).

tff(c_3864,plain,(
    v4_relat_1('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3860,c_143])).

tff(c_4134,plain,(
    v4_relat_1('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4130,c_3864])).

tff(c_4136,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_375,c_4134])).

tff(c_4137,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4122])).

tff(c_3923,plain,(
    ! [B_107] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_107,k1_xboole_0)))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3858,c_200])).

tff(c_4140,plain,(
    ! [B_107] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_107,'#skF_4')))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4137,c_3923])).

tff(c_4362,plain,(
    ! [A_335] :
      ( v1_funct_2('#skF_4',A_335,'#skF_4')
      | A_335 = '#skF_4'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_335,'#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4137,c_4137,c_4137,c_4137,c_4137,c_22])).

tff(c_4373,plain,(
    ! [B_336] :
      ( v1_funct_2('#skF_4',B_336,'#skF_4')
      | B_336 = '#skF_4'
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_336) ) ),
    inference(resolution,[status(thm)],[c_4140,c_4362])).

tff(c_4385,plain,
    ( v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_4')
    | k1_relat_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6,c_4373])).

tff(c_4386,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_4385])).

tff(c_4146,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4137,c_369])).

tff(c_4414,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4386,c_4146])).

tff(c_4433,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4414])).

tff(c_4434,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_4385])).

tff(c_4141,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4137,c_3921])).

tff(c_3862,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3860,c_162])).

tff(c_44,plain,(
    ! [A_26] :
      ( m1_subset_1(u1_pre_topc(A_26),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_26))))
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_145,plain,(
    ! [A_87,B_88] :
      ( v1_pre_topc(g1_pre_topc(A_87,B_88))
      | ~ m1_subset_1(B_88,k1_zfmisc_1(k1_zfmisc_1(A_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_149,plain,(
    ! [A_26] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_26),u1_pre_topc(A_26)))
      | ~ l1_pre_topc(A_26) ) ),
    inference(resolution,[status(thm)],[c_44,c_145])).

tff(c_3940,plain,
    ( v1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3858,c_149])).

tff(c_4469,plain,
    ( v1_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4137,c_3940])).

tff(c_4470,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_4469])).

tff(c_4473,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_120,c_4470])).

tff(c_4477,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_4473])).

tff(c_4479,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_4469])).

tff(c_3937,plain,
    ( v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3858,c_46])).

tff(c_5048,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4479,c_4137,c_3937])).

tff(c_5049,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_5048])).

tff(c_5052,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_5049])).

tff(c_5056,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_5052])).

tff(c_5058,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_5048])).

tff(c_4143,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4137,c_3858])).

tff(c_3896,plain,(
    ! [D_319,A_320,B_321] :
      ( v5_pre_topc(D_319,A_320,B_321)
      | ~ v5_pre_topc(D_319,g1_pre_topc(u1_struct_0(A_320),u1_pre_topc(A_320)),B_321)
      | ~ m1_subset_1(D_319,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_320),u1_pre_topc(A_320))),u1_struct_0(B_321))))
      | ~ v1_funct_2(D_319,u1_struct_0(g1_pre_topc(u1_struct_0(A_320),u1_pre_topc(A_320))),u1_struct_0(B_321))
      | ~ m1_subset_1(D_319,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_320),u1_struct_0(B_321))))
      | ~ v1_funct_2(D_319,u1_struct_0(A_320),u1_struct_0(B_321))
      | ~ v1_funct_1(D_319)
      | ~ l1_pre_topc(B_321)
      | ~ v2_pre_topc(B_321)
      | ~ l1_pre_topc(A_320)
      | ~ v2_pre_topc(A_320) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_3906,plain,(
    ! [A_320] :
      ( v5_pre_topc('#skF_4',A_320,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_320),u1_pre_topc(A_320)),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_320),u1_pre_topc(A_320))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_320),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_320),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_320)
      | ~ v2_pre_topc(A_320)
      | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0(A_320),u1_pre_topc(A_320)))) ) ),
    inference(resolution,[status(thm)],[c_200,c_3896])).

tff(c_3917,plain,(
    ! [A_320] :
      ( v5_pre_topc('#skF_4',A_320,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_320),u1_pre_topc(A_320)),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_320),u1_pre_topc(A_320))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_320),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_320),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_320)
      | ~ v2_pre_topc(A_320)
      | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0(A_320),u1_pre_topc(A_320)))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_3906])).

tff(c_5125,plain,(
    ! [A_378] :
      ( v5_pre_topc('#skF_4',A_378,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_378),u1_pre_topc(A_378)),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_378),u1_pre_topc(A_378))),'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_378),'#skF_4')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_378),'#skF_4')
      | ~ l1_pre_topc(A_378)
      | ~ v2_pre_topc(A_378)
      | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0(A_378),u1_pre_topc(A_378)))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5058,c_4479,c_4143,c_4143,c_4143,c_3917])).

tff(c_5134,plain,
    ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),'#skF_4')))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3860,c_5125])).

tff(c_5139,plain,
    ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_4')))
    | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3860,c_78,c_76,c_4434,c_3860,c_3860,c_4141,c_3860,c_3862,c_5134])).

tff(c_5140,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))) ),
    inference(splitLeft,[status(thm)],[c_5139])).

tff(c_5143,plain,
    ( ~ v4_relat_1('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_5140])).

tff(c_5147,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_3864,c_5143])).

tff(c_5148,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_4')))
    | v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_5139])).

tff(c_5223,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_5148])).

tff(c_5226,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_4140,c_5223])).

tff(c_5230,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_5226])).

tff(c_5232,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_5148])).

tff(c_5231,plain,(
    v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_5148])).

tff(c_54,plain,(
    ! [D_57,A_43,B_51] :
      ( v5_pre_topc(D_57,A_43,B_51)
      | ~ v5_pre_topc(D_57,A_43,g1_pre_topc(u1_struct_0(B_51),u1_pre_topc(B_51)))
      | ~ m1_subset_1(D_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_43),u1_struct_0(g1_pre_topc(u1_struct_0(B_51),u1_pre_topc(B_51))))))
      | ~ v1_funct_2(D_57,u1_struct_0(A_43),u1_struct_0(g1_pre_topc(u1_struct_0(B_51),u1_pre_topc(B_51))))
      | ~ m1_subset_1(D_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_43),u1_struct_0(B_51))))
      | ~ v1_funct_2(D_57,u1_struct_0(A_43),u1_struct_0(B_51))
      | ~ v1_funct_1(D_57)
      | ~ l1_pre_topc(B_51)
      | ~ v2_pre_topc(B_51)
      | ~ l1_pre_topc(A_43)
      | ~ v2_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_4183,plain,(
    ! [D_57,A_43] :
      ( v5_pre_topc(D_57,A_43,'#skF_2')
      | ~ v5_pre_topc(D_57,A_43,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ m1_subset_1(D_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_43),'#skF_4')))
      | ~ v1_funct_2(D_57,u1_struct_0(A_43),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1(D_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_43),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_57,u1_struct_0(A_43),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_57)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_43)
      | ~ v2_pre_topc(A_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4143,c_54])).

tff(c_5298,plain,(
    ! [D_381,A_382] :
      ( v5_pre_topc(D_381,A_382,'#skF_2')
      | ~ v5_pre_topc(D_381,A_382,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ m1_subset_1(D_381,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_382),'#skF_4')))
      | ~ v1_funct_2(D_381,u1_struct_0(A_382),'#skF_4')
      | ~ m1_subset_1(D_381,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_382),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_381,u1_struct_0(A_382),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_381)
      | ~ l1_pre_topc(A_382)
      | ~ v2_pre_topc(A_382) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_4143,c_4183])).

tff(c_5308,plain,(
    ! [A_382] :
      ( v5_pre_topc('#skF_4',A_382,'#skF_2')
      | ~ v5_pre_topc('#skF_4',A_382,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_382),'#skF_4')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_382),'#skF_4')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_382),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(A_382)
      | ~ v2_pre_topc(A_382)
      | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(A_382)) ) ),
    inference(resolution,[status(thm)],[c_201,c_5298])).

tff(c_5316,plain,(
    ! [A_383] :
      ( v5_pre_topc('#skF_4',A_383,'#skF_2')
      | ~ v5_pre_topc('#skF_4',A_383,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_383),'#skF_4')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_383),'#skF_4')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_383),u1_struct_0('#skF_2'))
      | ~ l1_pre_topc(A_383)
      | ~ v2_pre_topc(A_383)
      | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(A_383)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_5308])).

tff(c_5319,plain,
    ( v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),'#skF_4')))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_5231,c_5316])).

tff(c_5328,plain,(
    v5_pre_topc('#skF_4','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3860,c_78,c_76,c_3869,c_3860,c_4434,c_3860,c_5232,c_3860,c_5319])).

tff(c_5330,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_194,c_5328])).

tff(c_5331,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_433])).

tff(c_5362,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5331,c_87])).

tff(c_5360,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5331,c_91])).

tff(c_5435,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),k1_xboole_0)
    | u1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5360,c_24])).

tff(c_5461,plain,
    ( k1_xboole_0 = '#skF_4'
    | u1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5362,c_5435])).

tff(c_5470,plain,(
    u1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_5461])).

tff(c_5522,plain,(
    v4_relat_1('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5470,c_144])).

tff(c_5524,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_375,c_5522])).

tff(c_5525,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5461])).

tff(c_5533,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5525,c_5362])).

tff(c_5527,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),'#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5525,c_5360])).

tff(c_5536,plain,(
    u1_struct_0('#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5525,c_5331])).

tff(c_5677,plain,(
    u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5536,c_5525,c_3858])).

tff(c_5333,plain,(
    ! [D_384,A_385,B_386] :
      ( v5_pre_topc(D_384,A_385,B_386)
      | ~ v5_pre_topc(D_384,A_385,g1_pre_topc(u1_struct_0(B_386),u1_pre_topc(B_386)))
      | ~ m1_subset_1(D_384,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_385),u1_struct_0(g1_pre_topc(u1_struct_0(B_386),u1_pre_topc(B_386))))))
      | ~ v1_funct_2(D_384,u1_struct_0(A_385),u1_struct_0(g1_pre_topc(u1_struct_0(B_386),u1_pre_topc(B_386))))
      | ~ m1_subset_1(D_384,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_385),u1_struct_0(B_386))))
      | ~ v1_funct_2(D_384,u1_struct_0(A_385),u1_struct_0(B_386))
      | ~ v1_funct_1(D_384)
      | ~ l1_pre_topc(B_386)
      | ~ v2_pre_topc(B_386)
      | ~ l1_pre_topc(A_385)
      | ~ v2_pre_topc(A_385) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_5337,plain,(
    ! [A_385] :
      ( v5_pre_topc('#skF_4',A_385,'#skF_2')
      | ~ v5_pre_topc('#skF_4',A_385,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_385),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_385),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_385),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_385)
      | ~ v2_pre_topc(A_385)
      | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(A_385)) ) ),
    inference(resolution,[status(thm)],[c_200,c_5333])).

tff(c_5343,plain,(
    ! [A_385] :
      ( v5_pre_topc('#skF_4',A_385,'#skF_2')
      | ~ v5_pre_topc('#skF_4',A_385,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_385),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_385),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_385),u1_struct_0('#skF_2'))
      | ~ l1_pre_topc(A_385)
      | ~ v2_pre_topc(A_385)
      | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(A_385)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_64,c_5337])).

tff(c_6069,plain,(
    ! [A_416] :
      ( v5_pre_topc('#skF_4',A_416,'#skF_2')
      | ~ v5_pre_topc('#skF_4',A_416,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_416),'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_416),'#skF_4')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_416),'#skF_4')
      | ~ l1_pre_topc(A_416)
      | ~ v2_pre_topc(A_416)
      | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(A_416)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5536,c_5536,c_5677,c_5536,c_5536,c_5343])).

tff(c_6078,plain,
    ( v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_5527,c_6069])).

tff(c_6091,plain,
    ( v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_5533,c_6078])).

tff(c_6092,plain,
    ( ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_194,c_6091])).

tff(c_6097,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_6092])).

tff(c_6100,plain,
    ( ~ v4_relat_1('#skF_4',u1_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_6097])).

tff(c_6104,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_144,c_6100])).

tff(c_6105,plain,(
    ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_6092])).

tff(c_5372,plain,
    ( v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5331,c_46])).

tff(c_5389,plain,(
    v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_5372])).

tff(c_5530,plain,(
    v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5525,c_5389])).

tff(c_5361,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5331,c_62])).

tff(c_5534,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5525,c_5361])).

tff(c_5784,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5677,c_5534])).

tff(c_5355,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5331,c_162])).

tff(c_5862,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5525,c_5355])).

tff(c_5378,plain,
    ( l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5331,c_120])).

tff(c_5393,plain,(
    l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_5378])).

tff(c_5532,plain,(
    l1_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5525,c_5393])).

tff(c_5358,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5331,c_60])).

tff(c_5611,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5525,c_5358])).

tff(c_5614,plain,
    ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_5611,c_50])).

tff(c_5634,plain,
    ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
    | ~ v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_5532,c_64,c_5614])).

tff(c_6319,plain,(
    v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5530,c_5533,c_5677,c_5527,c_5677,c_5784,c_5677,c_5862,c_5634])).

tff(c_6320,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6105,c_6319])).

tff(c_6322,plain,(
    r1_tarski(k1_relat_1('#skF_4'),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_227])).

tff(c_6414,plain,(
    ! [B_441,A_442,C_443] :
      ( k1_xboole_0 = B_441
      | k1_relset_1(A_442,B_441,C_443) = A_442
      | ~ v1_funct_2(C_443,A_442,B_441)
      | ~ m1_subset_1(C_443,k1_zfmisc_1(k2_zfmisc_1(A_442,B_441))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_6426,plain,
    ( u1_struct_0('#skF_2') = k1_xboole_0
    | k1_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4') = u1_struct_0('#skF_1')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_91,c_6414])).

tff(c_6434,plain,
    ( u1_struct_0('#skF_2') = k1_xboole_0
    | u1_struct_0('#skF_1') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_173,c_6426])).

tff(c_6435,plain,(
    u1_struct_0('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_6434])).

tff(c_6444,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6435,c_87])).

tff(c_6442,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6435,c_91])).

tff(c_6423,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0
    | k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') = u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(resolution,[status(thm)],[c_60,c_6414])).

tff(c_6431,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_172,c_6423])).

tff(c_6540,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6435,c_6431])).

tff(c_6541,plain,(
    u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_6540])).

tff(c_6625,plain,(
    ! [D_447,A_448,B_449] :
      ( v5_pre_topc(D_447,A_448,B_449)
      | ~ v5_pre_topc(D_447,g1_pre_topc(u1_struct_0(A_448),u1_pre_topc(A_448)),B_449)
      | ~ m1_subset_1(D_447,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_448),u1_pre_topc(A_448))),u1_struct_0(B_449))))
      | ~ v1_funct_2(D_447,u1_struct_0(g1_pre_topc(u1_struct_0(A_448),u1_pre_topc(A_448))),u1_struct_0(B_449))
      | ~ m1_subset_1(D_447,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_448),u1_struct_0(B_449))))
      | ~ v1_funct_2(D_447,u1_struct_0(A_448),u1_struct_0(B_449))
      | ~ v1_funct_1(D_447)
      | ~ l1_pre_topc(B_449)
      | ~ v2_pre_topc(B_449)
      | ~ l1_pre_topc(A_448)
      | ~ v2_pre_topc(A_448) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_6634,plain,(
    ! [D_447,B_449] :
      ( v5_pre_topc(D_447,'#skF_1',B_449)
      | ~ v5_pre_topc(D_447,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_449)
      | ~ m1_subset_1(D_447,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(B_449))))
      | ~ v1_funct_2(D_447,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_449))
      | ~ m1_subset_1(D_447,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_449))))
      | ~ v1_funct_2(D_447,u1_struct_0('#skF_1'),u1_struct_0(B_449))
      | ~ v1_funct_1(D_447)
      | ~ l1_pre_topc(B_449)
      | ~ v2_pre_topc(B_449)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6435,c_6625])).

tff(c_9882,plain,(
    ! [D_642,B_643] :
      ( v5_pre_topc(D_642,'#skF_1',B_643)
      | ~ v5_pre_topc(D_642,g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),B_643)
      | ~ m1_subset_1(D_642,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_643))))
      | ~ v1_funct_2(D_642,k1_relat_1('#skF_4'),u1_struct_0(B_643))
      | ~ v1_funct_1(D_642)
      | ~ l1_pre_topc(B_643)
      | ~ v2_pre_topc(B_643) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_6435,c_6435,c_6541,c_6435,c_6541,c_6435,c_6634])).

tff(c_9891,plain,
    ( v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6442,c_9882])).

tff(c_9910,plain,
    ( v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_64,c_6444,c_9891])).

tff(c_9911,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_194,c_9910])).

tff(c_6450,plain,
    ( v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6435,c_46])).

tff(c_6463,plain,(
    v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_6450])).

tff(c_6456,plain,
    ( l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6435,c_120])).

tff(c_6467,plain,(
    l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_6456])).

tff(c_6443,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6435,c_62])).

tff(c_6589,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6541,c_6443])).

tff(c_6437,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6435,c_162])).

tff(c_9941,plain,(
    ! [D_644,A_645,B_646] :
      ( v5_pre_topc(D_644,A_645,B_646)
      | ~ v5_pre_topc(D_644,A_645,g1_pre_topc(u1_struct_0(B_646),u1_pre_topc(B_646)))
      | ~ m1_subset_1(D_644,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_645),u1_struct_0(g1_pre_topc(u1_struct_0(B_646),u1_pre_topc(B_646))))))
      | ~ v1_funct_2(D_644,u1_struct_0(A_645),u1_struct_0(g1_pre_topc(u1_struct_0(B_646),u1_pre_topc(B_646))))
      | ~ m1_subset_1(D_644,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_645),u1_struct_0(B_646))))
      | ~ v1_funct_2(D_644,u1_struct_0(A_645),u1_struct_0(B_646))
      | ~ v1_funct_1(D_644)
      | ~ l1_pre_topc(B_646)
      | ~ v2_pre_topc(B_646)
      | ~ l1_pre_topc(A_645)
      | ~ v2_pre_topc(A_645) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_9957,plain,(
    ! [A_645] :
      ( v5_pre_topc('#skF_4',A_645,'#skF_2')
      | ~ v5_pre_topc('#skF_4',A_645,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_645),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_645),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_645),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_645)
      | ~ v2_pre_topc(A_645)
      | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(A_645)) ) ),
    inference(resolution,[status(thm)],[c_200,c_9941])).

tff(c_10040,plain,(
    ! [A_656] :
      ( v5_pre_topc('#skF_4',A_656,'#skF_2')
      | ~ v5_pre_topc('#skF_4',A_656,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_656),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_656),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_656),u1_struct_0('#skF_2'))
      | ~ l1_pre_topc(A_656)
      | ~ v2_pre_topc(A_656)
      | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(A_656)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_64,c_9957])).

tff(c_10046,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2'))
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))
    | ~ v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))
    | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_6541,c_10040])).

tff(c_10052,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6541,c_6463,c_6467,c_6444,c_6541,c_6442,c_6541,c_6589,c_6437,c_10046])).

tff(c_10054,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9911,c_10052])).

tff(c_10055,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_6540])).

tff(c_312,plain,(
    ! [B_117] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_117,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_117) ) ),
    inference(resolution,[status(thm)],[c_60,c_195])).

tff(c_26,plain,(
    ! [C_20,B_19] :
      ( v1_funct_2(C_20,k1_xboole_0,B_19)
      | k1_relset_1(k1_xboole_0,B_19,C_20) != k1_xboole_0
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_340,plain,
    ( v1_funct_2('#skF_4',k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
    | k1_relset_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') != k1_xboole_0
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_312,c_26])).

tff(c_6386,plain,
    ( v1_funct_2('#skF_4',k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
    | k1_relset_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6322,c_340])).

tff(c_6387,plain,(
    k1_relset_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_6386])).

tff(c_10058,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10055,c_6387])).

tff(c_10134,plain,(
    ! [B_657] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_657,k1_xboole_0)))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_657) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10055,c_200])).

tff(c_10153,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_4',k1_xboole_0,k1_xboole_0)
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10134,c_30])).

tff(c_10182,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_4',k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6322,c_10153])).

tff(c_10183,plain,(
    ~ v1_funct_2('#skF_4',k1_xboole_0,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_10058,c_10182])).

tff(c_6439,plain,(
    v4_relat_1('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6435,c_143])).

tff(c_10057,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10055,c_6443])).

tff(c_10184,plain,(
    ! [B_657] :
      ( k1_xboole_0 = '#skF_4'
      | ~ v1_funct_2('#skF_4',B_657,k1_xboole_0)
      | k1_xboole_0 = B_657
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_657) ) ),
    inference(resolution,[status(thm)],[c_10134,c_24])).

tff(c_10270,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_10184])).

tff(c_10312,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10270,c_10055])).

tff(c_10060,plain,(
    ! [B_107] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_107,k1_xboole_0)))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10055,c_200])).

tff(c_10308,plain,(
    ! [B_107] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_107,'#skF_4')))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10270,c_10060])).

tff(c_18,plain,(
    ! [A_11,B_12,C_13] :
      ( k1_relset_1(A_11,B_12,C_13) = k1_relat_1(C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_342,plain,(
    ! [B_117] :
      ( k1_relset_1(B_117,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_117) ) ),
    inference(resolution,[status(thm)],[c_312,c_18])).

tff(c_6390,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_6387])).

tff(c_6392,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6322,c_6390])).

tff(c_10314,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10270,c_6392])).

tff(c_10591,plain,(
    ! [A_672] :
      ( v1_funct_2('#skF_4',A_672,'#skF_4')
      | A_672 = '#skF_4'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_672,'#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10270,c_10270,c_10270,c_10270,c_10270,c_22])).

tff(c_10602,plain,(
    ! [B_673] :
      ( v1_funct_2('#skF_4',B_673,'#skF_4')
      | B_673 = '#skF_4'
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_673) ) ),
    inference(resolution,[status(thm)],[c_10308,c_10591])).

tff(c_10613,plain,
    ( v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_4')
    | k1_relat_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6,c_10602])).

tff(c_10623,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_10314,c_10613])).

tff(c_10208,plain,(
    ! [D_659,A_660,B_661] :
      ( v5_pre_topc(D_659,A_660,B_661)
      | ~ v5_pre_topc(D_659,A_660,g1_pre_topc(u1_struct_0(B_661),u1_pre_topc(B_661)))
      | ~ m1_subset_1(D_659,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_660),u1_struct_0(g1_pre_topc(u1_struct_0(B_661),u1_pre_topc(B_661))))))
      | ~ v1_funct_2(D_659,u1_struct_0(A_660),u1_struct_0(g1_pre_topc(u1_struct_0(B_661),u1_pre_topc(B_661))))
      | ~ m1_subset_1(D_659,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_660),u1_struct_0(B_661))))
      | ~ v1_funct_2(D_659,u1_struct_0(A_660),u1_struct_0(B_661))
      | ~ v1_funct_1(D_659)
      | ~ l1_pre_topc(B_661)
      | ~ v2_pre_topc(B_661)
      | ~ l1_pre_topc(A_660)
      | ~ v2_pre_topc(A_660) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_10217,plain,(
    ! [D_659,A_660] :
      ( v5_pre_topc(D_659,A_660,'#skF_2')
      | ~ v5_pre_topc(D_659,A_660,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ m1_subset_1(D_659,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_660),k1_xboole_0)))
      | ~ v1_funct_2(D_659,u1_struct_0(A_660),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1(D_659,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_660),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_659,u1_struct_0(A_660),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_659)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_660)
      | ~ v2_pre_topc(A_660) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10055,c_10208])).

tff(c_10227,plain,(
    ! [D_659,A_660] :
      ( v5_pre_topc(D_659,A_660,'#skF_2')
      | ~ v5_pre_topc(D_659,A_660,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ m1_subset_1(D_659,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_660),k1_xboole_0)))
      | ~ v1_funct_2(D_659,u1_struct_0(A_660),k1_xboole_0)
      | ~ m1_subset_1(D_659,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_660),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_659,u1_struct_0(A_660),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_659)
      | ~ l1_pre_topc(A_660)
      | ~ v2_pre_topc(A_660) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_10055,c_10217])).

tff(c_11373,plain,(
    ! [D_718,A_719] :
      ( v5_pre_topc(D_718,A_719,'#skF_2')
      | ~ v5_pre_topc(D_718,A_719,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ m1_subset_1(D_718,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_719),'#skF_4')))
      | ~ v1_funct_2(D_718,u1_struct_0(A_719),'#skF_4')
      | ~ m1_subset_1(D_718,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_719),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_718,u1_struct_0(A_719),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_718)
      | ~ l1_pre_topc(A_719)
      | ~ v2_pre_topc(A_719) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10270,c_10270,c_10227])).

tff(c_11379,plain,(
    ! [D_718] :
      ( v5_pre_topc(D_718,'#skF_1','#skF_2')
      | ~ v5_pre_topc(D_718,'#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ m1_subset_1(D_718,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),'#skF_4')))
      | ~ v1_funct_2(D_718,u1_struct_0('#skF_1'),'#skF_4')
      | ~ m1_subset_1(D_718,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_718,u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_718)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6435,c_11373])).

tff(c_11489,plain,(
    ! [D_723] :
      ( v5_pre_topc(D_723,'#skF_1','#skF_2')
      | ~ v5_pre_topc(D_723,'#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ m1_subset_1(D_723,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_4')))
      | ~ v1_funct_2(D_723,k1_relat_1('#skF_4'),'#skF_4')
      | ~ m1_subset_1(D_723,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_723,k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_723) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_6435,c_6435,c_6435,c_11379])).

tff(c_11492,plain,
    ( v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_4')))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_4')
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6442,c_11489])).

tff(c_11499,plain,
    ( v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_6444,c_10623,c_11492])).

tff(c_11500,plain,
    ( ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_194,c_11499])).

tff(c_11505,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_11500])).

tff(c_11508,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_10308,c_11505])).

tff(c_11512,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_11508])).

tff(c_11513,plain,(
    ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_11500])).

tff(c_11514,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_11500])).

tff(c_10309,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10270,c_10057])).

tff(c_6441,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6435,c_60])).

tff(c_10091,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10055,c_6441])).

tff(c_10310,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),'#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10270,c_10091])).

tff(c_10080,plain,
    ( l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_10055,c_120])).

tff(c_11243,plain,
    ( l1_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10270,c_10080])).

tff(c_11244,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_11243])).

tff(c_11249,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_120,c_11244])).

tff(c_11253,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_11249])).

tff(c_11255,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_11243])).

tff(c_10074,plain,
    ( v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_10055,c_46])).

tff(c_11340,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11255,c_10270,c_10074])).

tff(c_11341,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_11340])).

tff(c_11344,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_11341])).

tff(c_11348,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_11344])).

tff(c_11350,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_11340])).

tff(c_28,plain,(
    ! [B_19,C_20,A_18] :
      ( k1_xboole_0 = B_19
      | v1_funct_2(C_20,A_18,B_19)
      | k1_relset_1(A_18,B_19,C_20) != A_18
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_338,plain,(
    ! [B_117] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0
      | v1_funct_2('#skF_4',B_117,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | k1_relset_1(B_117,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') != B_117
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_117) ) ),
    inference(resolution,[status(thm)],[c_312,c_28])).

tff(c_10379,plain,(
    ! [B_117] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = '#skF_4'
      | v1_funct_2('#skF_4',B_117,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | k1_relset_1(B_117,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') != B_117
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_117) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10270,c_338])).

tff(c_10380,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_10379])).

tff(c_10361,plain,(
    ! [D_666,A_667,B_668] :
      ( v5_pre_topc(D_666,A_667,B_668)
      | ~ v5_pre_topc(D_666,g1_pre_topc(u1_struct_0(A_667),u1_pre_topc(A_667)),B_668)
      | ~ m1_subset_1(D_666,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_667),u1_pre_topc(A_667))),u1_struct_0(B_668))))
      | ~ v1_funct_2(D_666,u1_struct_0(g1_pre_topc(u1_struct_0(A_667),u1_pre_topc(A_667))),u1_struct_0(B_668))
      | ~ m1_subset_1(D_666,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_667),u1_struct_0(B_668))))
      | ~ v1_funct_2(D_666,u1_struct_0(A_667),u1_struct_0(B_668))
      | ~ v1_funct_1(D_666)
      | ~ l1_pre_topc(B_668)
      | ~ v2_pre_topc(B_668)
      | ~ l1_pre_topc(A_667)
      | ~ v2_pre_topc(A_667) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_10364,plain,(
    ! [D_666,B_668] :
      ( v5_pre_topc(D_666,'#skF_1',B_668)
      | ~ v5_pre_topc(D_666,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_668)
      | ~ m1_subset_1(D_666,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(B_668))))
      | ~ v1_funct_2(D_666,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_668))
      | ~ m1_subset_1(D_666,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_668))))
      | ~ v1_funct_2(D_666,u1_struct_0('#skF_1'),u1_struct_0(B_668))
      | ~ v1_funct_1(D_666)
      | ~ l1_pre_topc(B_668)
      | ~ v2_pre_topc(B_668)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6435,c_10361])).

tff(c_11767,plain,(
    ! [D_741,B_742] :
      ( v5_pre_topc(D_741,'#skF_1',B_742)
      | ~ v5_pre_topc(D_741,g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),B_742)
      | ~ m1_subset_1(D_741,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(B_742))))
      | ~ v1_funct_2(D_741,u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(B_742))
      | ~ m1_subset_1(D_741,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_742))))
      | ~ v1_funct_2(D_741,k1_relat_1('#skF_4'),u1_struct_0(B_742))
      | ~ v1_funct_1(D_741)
      | ~ l1_pre_topc(B_742)
      | ~ v2_pre_topc(B_742) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_6435,c_6435,c_6435,c_6435,c_10364])).

tff(c_11770,plain,(
    ! [D_741] :
      ( v5_pre_topc(D_741,'#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc(D_741,g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ m1_subset_1(D_741,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),'#skF_4')))
      | ~ v1_funct_2(D_741,u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1(D_741,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))))
      | ~ v1_funct_2(D_741,k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ v1_funct_1(D_741)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10380,c_11767])).

tff(c_11930,plain,(
    ! [D_765] :
      ( v5_pre_topc(D_765,'#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc(D_765,g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ m1_subset_1(D_765,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),'#skF_4')))
      | ~ v1_funct_2(D_765,u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),'#skF_4')
      | ~ m1_subset_1(D_765,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_4')))
      | ~ v1_funct_2(D_765,k1_relat_1('#skF_4'),'#skF_4')
      | ~ v1_funct_1(D_765) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11350,c_11255,c_10380,c_10380,c_10380,c_11770])).

tff(c_11940,plain,
    ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),'#skF_4')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),'#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_4')))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_4')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6437,c_11930])).

tff(c_11948,plain,(
    v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_10623,c_11514,c_10309,c_10310,c_11940])).

tff(c_11950,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11513,c_11948])).

tff(c_11952,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_10379])).

tff(c_12037,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10312,c_11952])).

tff(c_12040,plain,(
    ! [B_766] :
      ( ~ v1_funct_2('#skF_4',B_766,k1_xboole_0)
      | k1_xboole_0 = B_766
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_766) ) ),
    inference(splitRight,[status(thm)],[c_10184])).

tff(c_12047,plain,(
    ! [A_3] :
      ( ~ v1_funct_2('#skF_4',A_3,k1_xboole_0)
      | k1_xboole_0 = A_3
      | ~ v4_relat_1('#skF_4',A_3)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_10,c_12040])).

tff(c_12062,plain,(
    ! [A_767] :
      ( ~ v1_funct_2('#skF_4',A_767,k1_xboole_0)
      | k1_xboole_0 = A_767
      | ~ v4_relat_1('#skF_4',A_767) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_12047])).

tff(c_12065,plain,
    ( u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) = k1_xboole_0
    | ~ v4_relat_1('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))) ),
    inference(resolution,[status(thm)],[c_10057,c_12062])).

tff(c_12068,plain,(
    u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6439,c_12065])).

tff(c_12070,plain,(
    v1_funct_2('#skF_4',k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12068,c_10057])).

tff(c_12076,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10183,c_12070])).

tff(c_12077,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_6434])).

tff(c_228,plain,(
    ! [B_110] :
      ( k1_relset_1(B_110,u1_struct_0('#skF_2'),'#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_110) ) ),
    inference(resolution,[status(thm)],[c_202,c_18])).

tff(c_6334,plain,(
    k1_relset_1(k1_xboole_0,u1_struct_0('#skF_2'),'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6322,c_228])).

tff(c_6321,plain,
    ( ~ v1_funct_2('#skF_4',k1_xboole_0,u1_struct_0('#skF_2'))
    | k1_relset_1(k1_xboole_0,u1_struct_0('#skF_2'),'#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_227])).

tff(c_6383,plain,
    ( ~ v1_funct_2('#skF_4',k1_xboole_0,u1_struct_0('#skF_2'))
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6334,c_6321])).

tff(c_6384,plain,(
    ~ v1_funct_2('#skF_4',k1_xboole_0,u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_6383])).

tff(c_12081,plain,(
    ~ v1_funct_2('#skF_4',k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12077,c_6384])).

tff(c_12097,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12077,c_87])).

tff(c_12095,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12077,c_91])).

tff(c_12175,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),k1_xboole_0)
    | u1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12095,c_24])).

tff(c_12201,plain,
    ( k1_xboole_0 = '#skF_4'
    | u1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12097,c_12175])).

tff(c_12210,plain,(
    u1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_12201])).

tff(c_12259,plain,(
    v1_funct_2('#skF_4',k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12210,c_12097])).

tff(c_12265,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12081,c_12259])).

tff(c_12266,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_12201])).

tff(c_12276,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12266,c_12097])).

tff(c_12268,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),'#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12266,c_12095])).

tff(c_12281,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12266,c_6392])).

tff(c_12089,plain,(
    ! [B_107] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_107,k1_xboole_0)))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12077,c_201])).

tff(c_12436,plain,(
    ! [B_107] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_107,'#skF_4')))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12266,c_12089])).

tff(c_12602,plain,(
    ! [A_784] :
      ( v1_funct_2('#skF_4',A_784,'#skF_4')
      | A_784 = '#skF_4'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_784,'#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12266,c_12266,c_12266,c_12266,c_12266,c_22])).

tff(c_12613,plain,(
    ! [B_785] :
      ( v1_funct_2('#skF_4',B_785,'#skF_4')
      | B_785 = '#skF_4'
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_785) ) ),
    inference(resolution,[status(thm)],[c_12436,c_12602])).

tff(c_12624,plain,
    ( v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_4')
    | k1_relat_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6,c_12613])).

tff(c_12634,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_12281,c_12624])).

tff(c_12279,plain,(
    u1_struct_0('#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12266,c_12077])).

tff(c_12665,plain,
    ( u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) = '#skF_4'
    | u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12279,c_12266,c_6431])).

tff(c_12666,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_12665])).

tff(c_12718,plain,
    ( l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_12666,c_120])).

tff(c_12861,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_12718])).

tff(c_12864,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_120,c_12861])).

tff(c_12868,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_12864])).

tff(c_12870,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_12718])).

tff(c_12712,plain,
    ( v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_12666,c_46])).

tff(c_13196,plain,
    ( v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12870,c_12712])).

tff(c_13197,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_13196])).

tff(c_13200,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_13197])).

tff(c_13204,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_13200])).

tff(c_13206,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_13196])).

tff(c_12096,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12077,c_62])).

tff(c_12275,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12266,c_12096])).

tff(c_12668,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12666,c_12275])).

tff(c_12090,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12077,c_162])).

tff(c_12553,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12266,c_12090])).

tff(c_12085,plain,(
    ! [B_107] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_107,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2'))))))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12077,c_200])).

tff(c_12559,plain,(
    ! [B_107] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_107,u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12266,c_12085])).

tff(c_12122,plain,(
    ! [D_768,A_769,B_770] :
      ( v5_pre_topc(D_768,A_769,B_770)
      | ~ v5_pre_topc(D_768,A_769,g1_pre_topc(u1_struct_0(B_770),u1_pre_topc(B_770)))
      | ~ m1_subset_1(D_768,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_769),u1_struct_0(g1_pre_topc(u1_struct_0(B_770),u1_pre_topc(B_770))))))
      | ~ v1_funct_2(D_768,u1_struct_0(A_769),u1_struct_0(g1_pre_topc(u1_struct_0(B_770),u1_pre_topc(B_770))))
      | ~ m1_subset_1(D_768,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_769),u1_struct_0(B_770))))
      | ~ v1_funct_2(D_768,u1_struct_0(A_769),u1_struct_0(B_770))
      | ~ v1_funct_1(D_768)
      | ~ l1_pre_topc(B_770)
      | ~ v2_pre_topc(B_770)
      | ~ l1_pre_topc(A_769)
      | ~ v2_pre_topc(A_769) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_12128,plain,(
    ! [D_768,A_769] :
      ( v5_pre_topc(D_768,A_769,'#skF_2')
      | ~ v5_pre_topc(D_768,A_769,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ m1_subset_1(D_768,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_769),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2'))))))
      | ~ v1_funct_2(D_768,u1_struct_0(A_769),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1(D_768,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_769),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_768,u1_struct_0(A_769),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_768)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_769)
      | ~ v2_pre_topc(A_769) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12077,c_12122])).

tff(c_12132,plain,(
    ! [D_768,A_769] :
      ( v5_pre_topc(D_768,A_769,'#skF_2')
      | ~ v5_pre_topc(D_768,A_769,g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2')))
      | ~ m1_subset_1(D_768,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_769),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2'))))))
      | ~ v1_funct_2(D_768,u1_struct_0(A_769),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1(D_768,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_769),k1_xboole_0)))
      | ~ v1_funct_2(D_768,u1_struct_0(A_769),k1_xboole_0)
      | ~ v1_funct_1(D_768)
      | ~ l1_pre_topc(A_769)
      | ~ v2_pre_topc(A_769) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_12077,c_12077,c_12077,c_12077,c_12128])).

tff(c_13273,plain,(
    ! [D_814,A_815] :
      ( v5_pre_topc(D_814,A_815,'#skF_2')
      | ~ v5_pre_topc(D_814,A_815,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ m1_subset_1(D_814,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_815),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))))
      | ~ v1_funct_2(D_814,u1_struct_0(A_815),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1(D_814,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_815),'#skF_4')))
      | ~ v1_funct_2(D_814,u1_struct_0(A_815),'#skF_4')
      | ~ v1_funct_1(D_814)
      | ~ l1_pre_topc(A_815)
      | ~ v2_pre_topc(A_815) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12266,c_12266,c_12266,c_12266,c_12266,c_12132])).

tff(c_13280,plain,(
    ! [A_815] :
      ( v5_pre_topc('#skF_4',A_815,'#skF_2')
      | ~ v5_pre_topc('#skF_4',A_815,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_815),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_815),'#skF_4')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_815),'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(A_815)
      | ~ v2_pre_topc(A_815)
      | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(A_815)) ) ),
    inference(resolution,[status(thm)],[c_12559,c_13273])).

tff(c_13306,plain,(
    ! [A_817] :
      ( v5_pre_topc('#skF_4',A_817,'#skF_2')
      | ~ v5_pre_topc('#skF_4',A_817,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_817),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_817),'#skF_4')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_817),'#skF_4')
      | ~ l1_pre_topc(A_817)
      | ~ v2_pre_topc(A_817)
      | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(A_817)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_13280])).

tff(c_13312,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_12666,c_13306])).

tff(c_13318,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_12666,c_13206,c_12870,c_12634,c_12666,c_12666,c_12668,c_12553,c_13312])).

tff(c_13321,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_13318])).

tff(c_13324,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_12436,c_13321])).

tff(c_13328,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_13324])).

tff(c_13330,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_13318])).

tff(c_13329,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_13318])).

tff(c_12697,plain,(
    ! [D_42,B_36] :
      ( v5_pre_topc(D_42,'#skF_1',B_36)
      | ~ v5_pre_topc(D_42,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_36)
      | ~ m1_subset_1(D_42,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_36))))
      | ~ v1_funct_2(D_42,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_36))
      | ~ m1_subset_1(D_42,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_36))))
      | ~ v1_funct_2(D_42,u1_struct_0('#skF_1'),u1_struct_0(B_36))
      | ~ v1_funct_1(D_42)
      | ~ l1_pre_topc(B_36)
      | ~ v2_pre_topc(B_36)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12666,c_50])).

tff(c_13212,plain,(
    ! [D_812,B_813] :
      ( v5_pre_topc(D_812,'#skF_1',B_813)
      | ~ v5_pre_topc(D_812,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_813)
      | ~ m1_subset_1(D_812,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_813))))
      | ~ v1_funct_2(D_812,k1_relat_1('#skF_4'),u1_struct_0(B_813))
      | ~ m1_subset_1(D_812,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_813))))
      | ~ v1_funct_2(D_812,u1_struct_0('#skF_1'),u1_struct_0(B_813))
      | ~ v1_funct_1(D_812)
      | ~ l1_pre_topc(B_813)
      | ~ v2_pre_topc(B_813) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_12666,c_12697])).

tff(c_13222,plain,(
    ! [D_812] :
      ( v5_pre_topc(D_812,'#skF_1','#skF_2')
      | ~ v5_pre_topc(D_812,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
      | ~ m1_subset_1(D_812,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_812,k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(D_812,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),'#skF_4')))
      | ~ v1_funct_2(D_812,u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_812)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12279,c_13212])).

tff(c_13229,plain,(
    ! [D_812] :
      ( v5_pre_topc(D_812,'#skF_1','#skF_2')
      | ~ v5_pre_topc(D_812,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
      | ~ m1_subset_1(D_812,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_4')))
      | ~ v1_funct_2(D_812,k1_relat_1('#skF_4'),'#skF_4')
      | ~ m1_subset_1(D_812,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),'#skF_4')))
      | ~ v1_funct_2(D_812,u1_struct_0('#skF_1'),'#skF_4')
      | ~ v1_funct_1(D_812) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_12279,c_12279,c_12279,c_13222])).

tff(c_13409,plain,
    ( v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_4')))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),'#skF_4')))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_13329,c_13229])).

tff(c_13412,plain,(
    v5_pre_topc('#skF_4','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_12276,c_12268,c_12634,c_13330,c_13409])).

tff(c_13414,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_194,c_13412])).

tff(c_13415,plain,(
    u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_12665])).

tff(c_13419,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13415,c_12275])).

tff(c_12093,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12077,c_60])).

tff(c_12366,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12266,c_12093])).

tff(c_13421,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13415,c_12366])).

tff(c_13630,plain,(
    ! [D_833,A_834] :
      ( v5_pre_topc(D_833,A_834,'#skF_2')
      | ~ v5_pre_topc(D_833,A_834,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ m1_subset_1(D_833,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_834),'#skF_4')))
      | ~ v1_funct_2(D_833,u1_struct_0(A_834),'#skF_4')
      | ~ m1_subset_1(D_833,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_834),'#skF_4')))
      | ~ v1_funct_2(D_833,u1_struct_0(A_834),'#skF_4')
      | ~ v1_funct_1(D_833)
      | ~ l1_pre_topc(A_834)
      | ~ v2_pre_topc(A_834) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12266,c_12266,c_13415,c_12266,c_13415,c_12266,c_12266,c_12132])).

tff(c_13632,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_13421,c_13630])).

tff(c_13644,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_13419,c_13421,c_12553,c_13632])).

tff(c_13656,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_13644])).

tff(c_13659,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_13656])).

tff(c_13663,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_13659])).

tff(c_13664,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_13644])).

tff(c_13667,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_13664])).

tff(c_13670,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_120,c_13667])).

tff(c_13674,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_13670])).

tff(c_13675,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_13664])).

tff(c_12147,plain,(
    ! [D_771,A_772,B_773] :
      ( v5_pre_topc(D_771,A_772,B_773)
      | ~ v5_pre_topc(D_771,g1_pre_topc(u1_struct_0(A_772),u1_pre_topc(A_772)),B_773)
      | ~ m1_subset_1(D_771,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_772),u1_pre_topc(A_772))),u1_struct_0(B_773))))
      | ~ v1_funct_2(D_771,u1_struct_0(g1_pre_topc(u1_struct_0(A_772),u1_pre_topc(A_772))),u1_struct_0(B_773))
      | ~ m1_subset_1(D_771,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_772),u1_struct_0(B_773))))
      | ~ v1_funct_2(D_771,u1_struct_0(A_772),u1_struct_0(B_773))
      | ~ v1_funct_1(D_771)
      | ~ l1_pre_topc(B_773)
      | ~ v2_pre_topc(B_773)
      | ~ l1_pre_topc(A_772)
      | ~ v2_pre_topc(A_772) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_12153,plain,(
    ! [D_771,A_772] :
      ( v5_pre_topc(D_771,A_772,'#skF_2')
      | ~ v5_pre_topc(D_771,g1_pre_topc(u1_struct_0(A_772),u1_pre_topc(A_772)),'#skF_2')
      | ~ m1_subset_1(D_771,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_772),u1_pre_topc(A_772))),k1_xboole_0)))
      | ~ v1_funct_2(D_771,u1_struct_0(g1_pre_topc(u1_struct_0(A_772),u1_pre_topc(A_772))),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(D_771,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_772),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_771,u1_struct_0(A_772),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_771)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_772)
      | ~ v2_pre_topc(A_772) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12077,c_12147])).

tff(c_12157,plain,(
    ! [D_771,A_772] :
      ( v5_pre_topc(D_771,A_772,'#skF_2')
      | ~ v5_pre_topc(D_771,g1_pre_topc(u1_struct_0(A_772),u1_pre_topc(A_772)),'#skF_2')
      | ~ m1_subset_1(D_771,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_772),u1_pre_topc(A_772))),k1_xboole_0)))
      | ~ v1_funct_2(D_771,u1_struct_0(g1_pre_topc(u1_struct_0(A_772),u1_pre_topc(A_772))),k1_xboole_0)
      | ~ m1_subset_1(D_771,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_772),k1_xboole_0)))
      | ~ v1_funct_2(D_771,u1_struct_0(A_772),k1_xboole_0)
      | ~ v1_funct_1(D_771)
      | ~ l1_pre_topc(A_772)
      | ~ v2_pre_topc(A_772) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_12077,c_12077,c_12077,c_12153])).

tff(c_13757,plain,(
    ! [D_845,A_846] :
      ( v5_pre_topc(D_845,A_846,'#skF_2')
      | ~ v5_pre_topc(D_845,g1_pre_topc(u1_struct_0(A_846),u1_pre_topc(A_846)),'#skF_2')
      | ~ m1_subset_1(D_845,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_846),u1_pre_topc(A_846))),'#skF_4')))
      | ~ v1_funct_2(D_845,u1_struct_0(g1_pre_topc(u1_struct_0(A_846),u1_pre_topc(A_846))),'#skF_4')
      | ~ m1_subset_1(D_845,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_846),'#skF_4')))
      | ~ v1_funct_2(D_845,u1_struct_0(A_846),'#skF_4')
      | ~ v1_funct_1(D_845)
      | ~ l1_pre_topc(A_846)
      | ~ v2_pre_topc(A_846) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12266,c_12266,c_12266,c_12266,c_12157])).

tff(c_13760,plain,
    ( v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),'#skF_4')))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_13421,c_13757])).

tff(c_13773,plain,(
    v5_pre_topc('#skF_4','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_64,c_12276,c_12268,c_13419,c_13675,c_13760])).

tff(c_13775,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_194,c_13773])).

tff(c_13777,plain,(
    k1_relset_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_6386])).

tff(c_13781,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_13777,c_342])).

tff(c_13788,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6322,c_13781])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6339,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6322,c_2])).

tff(c_6341,plain,(
    ~ r1_tarski(k1_xboole_0,k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_6339])).

tff(c_13793,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13788,c_6341])).

tff(c_13807,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_13793])).

tff(c_13808,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_6383])).

tff(c_13814,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13808,c_6341])).

tff(c_13828,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_13814])).

tff(c_13829,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_6339])).

tff(c_13841,plain,(
    k1_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_13829,c_173])).

tff(c_13951,plain,(
    ! [B_853,A_854,C_855] :
      ( k1_xboole_0 = B_853
      | k1_relset_1(A_854,B_853,C_855) = A_854
      | ~ v1_funct_2(C_855,A_854,B_853)
      | ~ m1_subset_1(C_855,k1_zfmisc_1(k2_zfmisc_1(A_854,B_853))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_13957,plain,
    ( u1_struct_0('#skF_2') = k1_xboole_0
    | k1_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4') = u1_struct_0('#skF_1')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_91,c_13951])).

tff(c_13963,plain,
    ( u1_struct_0('#skF_2') = k1_xboole_0
    | u1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_13841,c_13957])).

tff(c_13964,plain,(
    u1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_13963])).

tff(c_13856,plain,(
    ! [A_3] :
      ( r1_tarski(k1_xboole_0,A_3)
      | ~ v4_relat_1('#skF_4',A_3)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13829,c_10])).

tff(c_13887,plain,(
    ! [A_851] :
      ( r1_tarski(k1_xboole_0,A_851)
      | ~ v4_relat_1('#skF_4',A_851) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_13856])).

tff(c_13911,plain,(
    r1_tarski(k1_xboole_0,u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_144,c_13887])).

tff(c_13914,plain,
    ( u1_struct_0('#skF_1') = k1_xboole_0
    | ~ r1_tarski(u1_struct_0('#skF_1'),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_13911,c_2])).

tff(c_13923,plain,(
    ~ r1_tarski(u1_struct_0('#skF_1'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_13914])).

tff(c_13965,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13964,c_13923])).

tff(c_13978,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_13965])).

tff(c_13980,plain,(
    u1_struct_0('#skF_1') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_13963])).

tff(c_13979,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_13963])).

tff(c_14042,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13979,c_87])).

tff(c_14040,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13979,c_91])).

tff(c_14109,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),k1_xboole_0)
    | u1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14040,c_24])).

tff(c_14136,plain,
    ( k1_xboole_0 = '#skF_4'
    | u1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14042,c_14109])).

tff(c_14137,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_13980,c_14136])).

tff(c_14154,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14137,c_14042])).

tff(c_14146,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),'#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14137,c_14040])).

tff(c_14046,plain,
    ( v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_13979,c_46])).

tff(c_14059,plain,(
    v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_14046])).

tff(c_14153,plain,(
    v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14137,c_14059])).

tff(c_14052,plain,
    ( l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_13979,c_120])).

tff(c_14063,plain,(
    l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_14052])).

tff(c_14151,plain,(
    l1_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14137,c_14063])).

tff(c_14041,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13979,c_62])).

tff(c_14149,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14137,c_14041])).

tff(c_14157,plain,(
    u1_struct_0('#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14137,c_13979])).

tff(c_13833,plain,(
    k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_13829,c_172])).

tff(c_14428,plain,(
    k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14157,c_14137,c_13833])).

tff(c_14038,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13979,c_60])).

tff(c_14246,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14137,c_14038])).

tff(c_32,plain,(
    ! [B_19,A_18,C_20] :
      ( k1_xboole_0 = B_19
      | k1_relset_1(A_18,B_19,C_20) = A_18
      | ~ v1_funct_2(C_20,A_18,B_19)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_14727,plain,(
    ! [B_892,A_893,C_894] :
      ( B_892 = '#skF_4'
      | k1_relset_1(A_893,B_892,C_894) = A_893
      | ~ v1_funct_2(C_894,A_893,B_892)
      | ~ m1_subset_1(C_894,k1_zfmisc_1(k2_zfmisc_1(A_893,B_892))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14137,c_32])).

tff(c_14739,plain,
    ( u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) = '#skF_4'
    | k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))),'#skF_4') = u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))) ),
    inference(resolution,[status(thm)],[c_14246,c_14727])).

tff(c_14750,plain,
    ( u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) = '#skF_4'
    | u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14149,c_14428,c_14739])).

tff(c_14752,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_14750])).

tff(c_112,plain,(
    ! [B_77,A_78] :
      ( r1_tarski(k1_relat_1(B_77),A_78)
      | ~ v4_relat_1(B_77,A_78)
      | ~ v1_relat_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_115,plain,(
    ! [B_77,A_78] :
      ( k1_relat_1(B_77) = A_78
      | ~ r1_tarski(A_78,k1_relat_1(B_77))
      | ~ v4_relat_1(B_77,A_78)
      | ~ v1_relat_1(B_77) ) ),
    inference(resolution,[status(thm)],[c_112,c_2])).

tff(c_13847,plain,(
    ! [A_78] :
      ( k1_relat_1('#skF_4') = A_78
      | ~ r1_tarski(A_78,k1_xboole_0)
      | ~ v4_relat_1('#skF_4',A_78)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13829,c_115])).

tff(c_13924,plain,(
    ! [A_852] :
      ( k1_xboole_0 = A_852
      | ~ r1_tarski(A_852,k1_xboole_0)
      | ~ v4_relat_1('#skF_4',A_852) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_13829,c_13847])).

tff(c_13949,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = k1_xboole_0
    | ~ r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_143,c_13924])).

tff(c_14516,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = '#skF_4'
    | ~ r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14137,c_14137,c_13949])).

tff(c_14517,plain,(
    ~ r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_14516])).

tff(c_14753,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14752,c_14517])).

tff(c_14762,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_14753])).

tff(c_14764,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_14750])).

tff(c_247,plain,(
    ! [B_112] :
      ( k1_relset_1(B_112,u1_struct_0('#skF_2'),'#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_112) ) ),
    inference(resolution,[status(thm)],[c_202,c_18])).

tff(c_251,plain,(
    ! [A_3] :
      ( k1_relset_1(A_3,u1_struct_0('#skF_2'),'#skF_4') = k1_relat_1('#skF_4')
      | ~ v4_relat_1('#skF_4',A_3)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_10,c_247])).

tff(c_258,plain,(
    ! [A_3] :
      ( k1_relset_1(A_3,u1_struct_0('#skF_2'),'#skF_4') = k1_relat_1('#skF_4')
      | ~ v4_relat_1('#skF_4',A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_251])).

tff(c_13835,plain,(
    ! [A_3] :
      ( k1_relset_1(A_3,u1_struct_0('#skF_2'),'#skF_4') = k1_xboole_0
      | ~ v4_relat_1('#skF_4',A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13829,c_258])).

tff(c_14452,plain,(
    ! [A_873] :
      ( k1_relset_1(A_873,'#skF_4','#skF_4') = '#skF_4'
      | ~ v4_relat_1('#skF_4',A_873) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14157,c_14137,c_13835])).

tff(c_14475,plain,(
    k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_143,c_14452])).

tff(c_14763,plain,(
    u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_14750])).

tff(c_13954,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0
    | k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') = u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(resolution,[status(thm)],[c_60,c_13951])).

tff(c_13960,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0
    | k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') = u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_13954])).

tff(c_14397,plain,
    ( u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) = '#skF_4'
    | k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))),'#skF_4') = u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14157,c_14157,c_14137,c_13960])).

tff(c_14398,plain,(
    k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))),'#skF_4') = u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_14397])).

tff(c_14916,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14475,c_14763,c_14398])).

tff(c_14917,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14764,c_14916])).

tff(c_14918,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_14516])).

tff(c_14166,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14137,c_13829])).

tff(c_259,plain,(
    k1_relset_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'),'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_247])).

tff(c_13836,plain,(
    k1_relset_1(k1_xboole_0,u1_struct_0('#skF_2'),'#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_13829,c_13829,c_259])).

tff(c_14035,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_13979,c_13836])).

tff(c_14155,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14137,c_14137,c_14137,c_14035])).

tff(c_226,plain,
    ( v1_funct_2('#skF_4',k1_xboole_0,u1_struct_0('#skF_2'))
    | k1_relset_1(k1_xboole_0,u1_struct_0('#skF_2'),'#skF_4') != k1_xboole_0
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_202,c_26])).

tff(c_14999,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_14137,c_14166,c_14137,c_14155,c_14137,c_14157,c_14137,c_14157,c_226])).

tff(c_20,plain,(
    ! [D_17,B_15,C_16,A_14] :
      ( m1_subset_1(D_17,k1_zfmisc_1(k2_zfmisc_1(B_15,C_16)))
      | ~ r1_tarski(k1_relat_1(D_17),B_15)
      | ~ m1_subset_1(D_17,k1_zfmisc_1(k2_zfmisc_1(A_14,C_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_14106,plain,(
    ! [B_15] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_15,k1_xboole_0)))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_15) ) ),
    inference(resolution,[status(thm)],[c_14040,c_20])).

tff(c_14133,plain,(
    ! [B_15] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_15,k1_xboole_0)))
      | ~ r1_tarski(k1_xboole_0,B_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13829,c_14106])).

tff(c_14478,plain,(
    ! [B_15] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_15,'#skF_4')))
      | ~ r1_tarski('#skF_4',B_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14137,c_14137,c_14133])).

tff(c_14071,plain,(
    ! [D_857,A_858,B_859] :
      ( v5_pre_topc(D_857,A_858,B_859)
      | ~ v5_pre_topc(D_857,g1_pre_topc(u1_struct_0(A_858),u1_pre_topc(A_858)),B_859)
      | ~ m1_subset_1(D_857,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_858),u1_pre_topc(A_858))),u1_struct_0(B_859))))
      | ~ v1_funct_2(D_857,u1_struct_0(g1_pre_topc(u1_struct_0(A_858),u1_pre_topc(A_858))),u1_struct_0(B_859))
      | ~ m1_subset_1(D_857,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_858),u1_struct_0(B_859))))
      | ~ v1_funct_2(D_857,u1_struct_0(A_858),u1_struct_0(B_859))
      | ~ v1_funct_1(D_857)
      | ~ l1_pre_topc(B_859)
      | ~ v2_pre_topc(B_859)
      | ~ l1_pre_topc(A_858)
      | ~ v2_pre_topc(A_858) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_14077,plain,(
    ! [D_857,A_858] :
      ( v5_pre_topc(D_857,A_858,'#skF_2')
      | ~ v5_pre_topc(D_857,g1_pre_topc(u1_struct_0(A_858),u1_pre_topc(A_858)),'#skF_2')
      | ~ m1_subset_1(D_857,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_858),u1_pre_topc(A_858))),k1_xboole_0)))
      | ~ v1_funct_2(D_857,u1_struct_0(g1_pre_topc(u1_struct_0(A_858),u1_pre_topc(A_858))),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(D_857,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_858),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_857,u1_struct_0(A_858),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_857)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_858)
      | ~ v2_pre_topc(A_858) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13979,c_14071])).

tff(c_14081,plain,(
    ! [D_857,A_858] :
      ( v5_pre_topc(D_857,A_858,'#skF_2')
      | ~ v5_pre_topc(D_857,g1_pre_topc(u1_struct_0(A_858),u1_pre_topc(A_858)),'#skF_2')
      | ~ m1_subset_1(D_857,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_858),u1_pre_topc(A_858))),k1_xboole_0)))
      | ~ v1_funct_2(D_857,u1_struct_0(g1_pre_topc(u1_struct_0(A_858),u1_pre_topc(A_858))),k1_xboole_0)
      | ~ m1_subset_1(D_857,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_858),k1_xboole_0)))
      | ~ v1_funct_2(D_857,u1_struct_0(A_858),k1_xboole_0)
      | ~ v1_funct_1(D_857)
      | ~ l1_pre_topc(A_858)
      | ~ v2_pre_topc(A_858) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_13979,c_13979,c_13979,c_14077])).

tff(c_16036,plain,(
    ! [D_983,A_984] :
      ( v5_pre_topc(D_983,A_984,'#skF_2')
      | ~ v5_pre_topc(D_983,g1_pre_topc(u1_struct_0(A_984),u1_pre_topc(A_984)),'#skF_2')
      | ~ m1_subset_1(D_983,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_984),u1_pre_topc(A_984))),'#skF_4')))
      | ~ v1_funct_2(D_983,u1_struct_0(g1_pre_topc(u1_struct_0(A_984),u1_pre_topc(A_984))),'#skF_4')
      | ~ m1_subset_1(D_983,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_984),'#skF_4')))
      | ~ v1_funct_2(D_983,u1_struct_0(A_984),'#skF_4')
      | ~ v1_funct_1(D_983)
      | ~ l1_pre_topc(A_984)
      | ~ v2_pre_topc(A_984) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14137,c_14137,c_14137,c_14137,c_14081])).

tff(c_16046,plain,(
    ! [A_984] :
      ( v5_pre_topc('#skF_4',A_984,'#skF_2')
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_984),u1_pre_topc(A_984)),'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_984),u1_pre_topc(A_984))),'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_984),'#skF_4')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_984),'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(A_984)
      | ~ v2_pre_topc(A_984)
      | ~ r1_tarski('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_984),u1_pre_topc(A_984)))) ) ),
    inference(resolution,[status(thm)],[c_14478,c_16036])).

tff(c_16079,plain,(
    ! [A_989] :
      ( v5_pre_topc('#skF_4',A_989,'#skF_2')
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_989),u1_pre_topc(A_989)),'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_989),u1_pre_topc(A_989))),'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_989),'#skF_4')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_989),'#skF_4')
      | ~ l1_pre_topc(A_989)
      | ~ v2_pre_topc(A_989)
      | ~ r1_tarski('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_989),u1_pre_topc(A_989)))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_16046])).

tff(c_16091,plain,
    ( v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ v1_funct_2('#skF_4','#skF_4','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),'#skF_4')))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ r1_tarski('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_14918,c_16079])).

tff(c_16100,plain,
    ( v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_14918,c_78,c_76,c_14154,c_14146,c_14999,c_16091])).

tff(c_16101,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_194,c_16100])).

tff(c_14974,plain,
    ( l1_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_14918,c_120])).

tff(c_15214,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_14974])).

tff(c_15219,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_120,c_15214])).

tff(c_15223,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_15219])).

tff(c_15225,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_14974])).

tff(c_14968,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_14918,c_46])).

tff(c_15889,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15225,c_14968])).

tff(c_15890,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_15889])).

tff(c_15893,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_15890])).

tff(c_15897,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_15893])).

tff(c_15899,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_15889])).

tff(c_14923,plain,(
    v1_funct_2('#skF_4','#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14918,c_14149])).

tff(c_13834,plain,(
    ! [B_107] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_107,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))))
      | ~ r1_tarski(k1_xboole_0,B_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13829,c_200])).

tff(c_14033,plain,(
    ! [B_107] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_107,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2'))))))
      | ~ r1_tarski(k1_xboole_0,B_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13979,c_13834])).

tff(c_15072,plain,(
    ! [B_107] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_107,u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))))
      | ~ r1_tarski('#skF_4',B_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14137,c_14137,c_14033])).

tff(c_14312,plain,(
    ! [D_867,A_868,B_869] :
      ( v5_pre_topc(D_867,A_868,g1_pre_topc(u1_struct_0(B_869),u1_pre_topc(B_869)))
      | ~ v5_pre_topc(D_867,A_868,B_869)
      | ~ m1_subset_1(D_867,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_868),u1_struct_0(g1_pre_topc(u1_struct_0(B_869),u1_pre_topc(B_869))))))
      | ~ v1_funct_2(D_867,u1_struct_0(A_868),u1_struct_0(g1_pre_topc(u1_struct_0(B_869),u1_pre_topc(B_869))))
      | ~ m1_subset_1(D_867,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_868),u1_struct_0(B_869))))
      | ~ v1_funct_2(D_867,u1_struct_0(A_868),u1_struct_0(B_869))
      | ~ v1_funct_1(D_867)
      | ~ l1_pre_topc(B_869)
      | ~ v2_pre_topc(B_869)
      | ~ l1_pre_topc(A_868)
      | ~ v2_pre_topc(A_868) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_14318,plain,(
    ! [D_867,A_868] :
      ( v5_pre_topc(D_867,A_868,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc(D_867,A_868,'#skF_2')
      | ~ m1_subset_1(D_867,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_868),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))))
      | ~ v1_funct_2(D_867,u1_struct_0(A_868),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1(D_867,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_868),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_867,u1_struct_0(A_868),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_867)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_868)
      | ~ v2_pre_topc(A_868) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14157,c_14312])).

tff(c_16130,plain,(
    ! [D_991,A_992] :
      ( v5_pre_topc(D_991,A_992,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc(D_991,A_992,'#skF_2')
      | ~ m1_subset_1(D_991,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_992),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))))
      | ~ v1_funct_2(D_991,u1_struct_0(A_992),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1(D_991,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_992),'#skF_4')))
      | ~ v1_funct_2(D_991,u1_struct_0(A_992),'#skF_4')
      | ~ v1_funct_1(D_991)
      | ~ l1_pre_topc(A_992)
      | ~ v2_pre_topc(A_992) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_14157,c_14157,c_14157,c_14157,c_14318])).

tff(c_16134,plain,(
    ! [A_992] :
      ( v5_pre_topc('#skF_4',A_992,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc('#skF_4',A_992,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_992),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_992),'#skF_4')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_992),'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(A_992)
      | ~ v2_pre_topc(A_992)
      | ~ r1_tarski('#skF_4',u1_struct_0(A_992)) ) ),
    inference(resolution,[status(thm)],[c_15072,c_16130])).

tff(c_16148,plain,(
    ! [A_993] :
      ( v5_pre_topc('#skF_4',A_993,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc('#skF_4',A_993,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_993),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_993),'#skF_4')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_993),'#skF_4')
      | ~ l1_pre_topc(A_993)
      | ~ v2_pre_topc(A_993)
      | ~ r1_tarski('#skF_4',u1_struct_0(A_993)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_16134])).

tff(c_16157,plain,
    ( v5_pre_topc('#skF_4','#skF_2',g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_4','#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),'#skF_4')))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),'#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | ~ r1_tarski('#skF_4',u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_14157,c_16148])).

tff(c_16162,plain,
    ( v5_pre_topc('#skF_4','#skF_2',g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4','#skF_2','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_14157,c_74,c_72,c_14999,c_14157,c_14157,c_14923,c_16157])).

tff(c_16163,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_16162])).

tff(c_16166,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_14478,c_16163])).

tff(c_16170,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_16166])).

tff(c_16172,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_16162])).

tff(c_14036,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13979,c_162])).

tff(c_15034,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14137,c_14036])).

tff(c_14293,plain,(
    ! [D_863,A_864,B_865] :
      ( v5_pre_topc(D_863,A_864,B_865)
      | ~ v5_pre_topc(D_863,A_864,g1_pre_topc(u1_struct_0(B_865),u1_pre_topc(B_865)))
      | ~ m1_subset_1(D_863,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_864),u1_struct_0(g1_pre_topc(u1_struct_0(B_865),u1_pre_topc(B_865))))))
      | ~ v1_funct_2(D_863,u1_struct_0(A_864),u1_struct_0(g1_pre_topc(u1_struct_0(B_865),u1_pre_topc(B_865))))
      | ~ m1_subset_1(D_863,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_864),u1_struct_0(B_865))))
      | ~ v1_funct_2(D_863,u1_struct_0(A_864),u1_struct_0(B_865))
      | ~ v1_funct_1(D_863)
      | ~ l1_pre_topc(B_865)
      | ~ v2_pre_topc(B_865)
      | ~ l1_pre_topc(A_864)
      | ~ v2_pre_topc(A_864) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_14299,plain,(
    ! [D_863,A_864] :
      ( v5_pre_topc(D_863,A_864,'#skF_2')
      | ~ v5_pre_topc(D_863,A_864,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ m1_subset_1(D_863,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_864),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))))
      | ~ v1_funct_2(D_863,u1_struct_0(A_864),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1(D_863,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_864),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_863,u1_struct_0(A_864),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_863)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_864)
      | ~ v2_pre_topc(A_864) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14157,c_14293])).

tff(c_16324,plain,(
    ! [D_1001,A_1002] :
      ( v5_pre_topc(D_1001,A_1002,'#skF_2')
      | ~ v5_pre_topc(D_1001,A_1002,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ m1_subset_1(D_1001,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1002),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))))
      | ~ v1_funct_2(D_1001,u1_struct_0(A_1002),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1(D_1001,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1002),'#skF_4')))
      | ~ v1_funct_2(D_1001,u1_struct_0(A_1002),'#skF_4')
      | ~ v1_funct_1(D_1001)
      | ~ l1_pre_topc(A_1002)
      | ~ v2_pre_topc(A_1002) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_14157,c_14157,c_14157,c_14157,c_14299])).

tff(c_16328,plain,(
    ! [A_1002] :
      ( v5_pre_topc('#skF_4',A_1002,'#skF_2')
      | ~ v5_pre_topc('#skF_4',A_1002,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1002),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1002),'#skF_4')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1002),'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(A_1002)
      | ~ v2_pre_topc(A_1002)
      | ~ r1_tarski('#skF_4',u1_struct_0(A_1002)) ) ),
    inference(resolution,[status(thm)],[c_15072,c_16324])).

tff(c_16342,plain,(
    ! [A_1003] :
      ( v5_pre_topc('#skF_4',A_1003,'#skF_2')
      | ~ v5_pre_topc('#skF_4',A_1003,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1003),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1003),'#skF_4')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1003),'#skF_4')
      | ~ l1_pre_topc(A_1003)
      | ~ v2_pre_topc(A_1003)
      | ~ r1_tarski('#skF_4',u1_struct_0(A_1003)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_16328])).

tff(c_16348,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ v1_funct_2('#skF_4','#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ r1_tarski('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_14918,c_16342])).

tff(c_16354,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_14918,c_15899,c_15225,c_14999,c_14918,c_16172,c_14918,c_14923,c_15034,c_16348])).

tff(c_16356,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16101,c_16354])).

tff(c_16357,plain,(
    u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_14397])).

tff(c_16360,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16357,c_14149])).

tff(c_16555,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14137,c_14036])).

tff(c_14252,plain,
    ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14246,c_50])).

tff(c_14275,plain,
    ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
    | ~ l1_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_64,c_14252])).

tff(c_16899,plain,(
    v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14153,c_14151,c_14154,c_16357,c_14146,c_16357,c_16360,c_16357,c_16555,c_14275])).

tff(c_14303,plain,(
    ! [D_863,A_864] :
      ( v5_pre_topc(D_863,A_864,'#skF_2')
      | ~ v5_pre_topc(D_863,A_864,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ m1_subset_1(D_863,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_864),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))))
      | ~ v1_funct_2(D_863,u1_struct_0(A_864),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1(D_863,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_864),'#skF_4')))
      | ~ v1_funct_2(D_863,u1_struct_0(A_864),'#skF_4')
      | ~ v1_funct_1(D_863)
      | ~ l1_pre_topc(A_864)
      | ~ v2_pre_topc(A_864) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_14157,c_14157,c_14157,c_14157,c_14299])).

tff(c_17003,plain,(
    ! [D_1045,A_1046] :
      ( v5_pre_topc(D_1045,A_1046,'#skF_2')
      | ~ v5_pre_topc(D_1045,A_1046,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ m1_subset_1(D_1045,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1046),'#skF_4')))
      | ~ v1_funct_2(D_1045,u1_struct_0(A_1046),'#skF_4')
      | ~ m1_subset_1(D_1045,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1046),'#skF_4')))
      | ~ v1_funct_2(D_1045,u1_struct_0(A_1046),'#skF_4')
      | ~ v1_funct_1(D_1045)
      | ~ l1_pre_topc(A_1046)
      | ~ v2_pre_topc(A_1046) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16357,c_16357,c_14303])).

tff(c_17012,plain,
    ( v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),'#skF_4')))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14146,c_17003])).

tff(c_17026,plain,(
    v5_pre_topc('#skF_4','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_64,c_14154,c_14146,c_16899,c_17012])).

tff(c_17028,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_194,c_17026])).

tff(c_17029,plain,(
    u1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_13914])).

tff(c_17037,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17029,c_60])).

tff(c_17210,plain,(
    k1_relset_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_17037,c_18])).

tff(c_17231,plain,(
    k1_relset_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_13829,c_17210])).

tff(c_17039,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17029,c_62])).

tff(c_17199,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0
    | k1_relset_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(resolution,[status(thm)],[c_17037,c_32])).

tff(c_17222,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0
    | k1_relset_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17039,c_17199])).

tff(c_20538,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_17231,c_17222])).

tff(c_20539,plain,(
    u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1'))) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_20538])).

tff(c_13910,plain,(
    r1_tarski(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(resolution,[status(thm)],[c_143,c_13887])).

tff(c_17032,plain,(
    r1_tarski(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17029,c_13910])).

tff(c_17136,plain,
    ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1'))) = k1_xboole_0
    | ~ r1_tarski(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1'))),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_17032,c_2])).

tff(c_17354,plain,(
    ~ r1_tarski(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1'))),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_17136])).

tff(c_20541,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20539,c_17354])).

tff(c_20549,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_20541])).

tff(c_20551,plain,(
    u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1'))) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_20538])).

tff(c_20550,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_20538])).

tff(c_20559,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1'))),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20550,c_17039])).

tff(c_20558,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1'))),k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20550,c_17037])).

tff(c_20721,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1'))),k1_xboole_0)
    | u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1'))) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20558,c_24])).

tff(c_20748,plain,
    ( k1_xboole_0 = '#skF_4'
    | u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20559,c_20721])).

tff(c_20749,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_20551,c_20748])).

tff(c_20766,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20749,c_20550])).

tff(c_17038,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17029,c_91])).

tff(c_20780,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4',u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20749,c_17038])).

tff(c_13832,plain,(
    ! [B_117] :
      ( k1_relset_1(B_117,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,B_117) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13829,c_13829,c_342])).

tff(c_341,plain,
    ( k1_relset_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_4',k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_312,c_30])).

tff(c_17483,plain,
    ( k1_relset_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_4',k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_13829,c_341])).

tff(c_17484,plain,(
    ~ v1_funct_2('#skF_4',k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_17483])).

tff(c_18498,plain,
    ( v1_funct_2('#skF_4',k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
    | k1_relset_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_13829,c_340])).

tff(c_18499,plain,(
    k1_relset_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_17484,c_18498])).

tff(c_18502,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_13832,c_18499])).

tff(c_18506,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_18502])).

tff(c_18508,plain,(
    v1_funct_2('#skF_4',k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_17483])).

tff(c_20554,plain,(
    v1_funct_2('#skF_4',k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20550,c_18508])).

tff(c_20764,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20749,c_20749,c_20554])).

tff(c_17355,plain,(
    ! [B_1061] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_1061,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))))
      | ~ r1_tarski(k1_xboole_0,B_1061) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13829,c_200])).

tff(c_17405,plain,(
    ! [B_1061] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0
      | v1_funct_2('#skF_4',B_1061,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | k1_relset_1(B_1061,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') != B_1061
      | ~ r1_tarski(k1_xboole_0,B_1061) ) ),
    inference(resolution,[status(thm)],[c_17355,c_28])).

tff(c_20802,plain,(
    ! [B_1061] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = '#skF_4'
      | v1_funct_2('#skF_4',B_1061,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | k1_relset_1(B_1061,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') != B_1061
      | ~ r1_tarski('#skF_4',B_1061) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20749,c_20749,c_17405])).

tff(c_20803,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_20802])).

tff(c_20787,plain,(
    u1_struct_0('#skF_1') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20749,c_17029])).

tff(c_17040,plain,(
    v1_funct_2('#skF_4',k1_xboole_0,u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17029,c_87])).

tff(c_20785,plain,(
    v1_funct_2('#skF_4','#skF_4',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20749,c_17040])).

tff(c_20508,plain,(
    ! [D_1158,A_1159,B_1160] :
      ( v5_pre_topc(D_1158,A_1159,B_1160)
      | ~ v5_pre_topc(D_1158,A_1159,g1_pre_topc(u1_struct_0(B_1160),u1_pre_topc(B_1160)))
      | ~ m1_subset_1(D_1158,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1159),u1_struct_0(g1_pre_topc(u1_struct_0(B_1160),u1_pre_topc(B_1160))))))
      | ~ v1_funct_2(D_1158,u1_struct_0(A_1159),u1_struct_0(g1_pre_topc(u1_struct_0(B_1160),u1_pre_topc(B_1160))))
      | ~ m1_subset_1(D_1158,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1159),u1_struct_0(B_1160))))
      | ~ v1_funct_2(D_1158,u1_struct_0(A_1159),u1_struct_0(B_1160))
      | ~ v1_funct_1(D_1158)
      | ~ l1_pre_topc(B_1160)
      | ~ v2_pre_topc(B_1160)
      | ~ l1_pre_topc(A_1159)
      | ~ v2_pre_topc(A_1159) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_20512,plain,(
    ! [A_1159] :
      ( v5_pre_topc('#skF_4',A_1159,'#skF_2')
      | ~ v5_pre_topc('#skF_4',A_1159,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1159),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1159),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1159),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_1159)
      | ~ v2_pre_topc(A_1159)
      | ~ r1_tarski(k1_xboole_0,u1_struct_0(A_1159)) ) ),
    inference(resolution,[status(thm)],[c_13834,c_20508])).

tff(c_20524,plain,(
    ! [A_1159] :
      ( v5_pre_topc('#skF_4',A_1159,'#skF_2')
      | ~ v5_pre_topc('#skF_4',A_1159,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1159),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1159),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1159),u1_struct_0('#skF_2'))
      | ~ l1_pre_topc(A_1159)
      | ~ v2_pre_topc(A_1159)
      | ~ r1_tarski(k1_xboole_0,u1_struct_0(A_1159)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_64,c_20512])).

tff(c_20943,plain,(
    ! [A_1167] :
      ( v5_pre_topc('#skF_4',A_1167,'#skF_2')
      | ~ v5_pre_topc('#skF_4',A_1167,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1167),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1167),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1167),u1_struct_0('#skF_2'))
      | ~ l1_pre_topc(A_1167)
      | ~ v2_pre_topc(A_1167)
      | ~ r1_tarski('#skF_4',u1_struct_0(A_1167)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20749,c_20524])).

tff(c_20946,plain,
    ( v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v1_funct_2('#skF_4','#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ r1_tarski('#skF_4',u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_20787,c_20943])).

tff(c_20948,plain,
    ( v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v1_funct_2('#skF_4','#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4',u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_20787,c_78,c_76,c_20785,c_20787,c_20787,c_20946])).

tff(c_20949,plain,
    ( ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v1_funct_2('#skF_4','#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4',u1_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_194,c_20948])).

tff(c_21355,plain,(
    ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20780,c_20764,c_20803,c_20949])).

tff(c_20779,plain,(
    r1_tarski('#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20749,c_20749,c_17032])).

tff(c_20556,plain,(
    ! [B_107] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_107,k1_xboole_0)))
      | ~ r1_tarski(k1_xboole_0,B_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20550,c_13834])).

tff(c_20759,plain,(
    ! [B_107] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_107,'#skF_4')))
      | ~ r1_tarski('#skF_4',B_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20749,c_20749,c_20556])).

tff(c_20761,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20749,c_20749,c_20559])).

tff(c_20758,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),'#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20749,c_20749,c_20558])).

tff(c_17137,plain,(
    ! [D_1050,A_1051,B_1052] :
      ( v5_pre_topc(D_1050,A_1051,B_1052)
      | ~ v5_pre_topc(D_1050,g1_pre_topc(u1_struct_0(A_1051),u1_pre_topc(A_1051)),B_1052)
      | ~ m1_subset_1(D_1050,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1051),u1_pre_topc(A_1051))),u1_struct_0(B_1052))))
      | ~ v1_funct_2(D_1050,u1_struct_0(g1_pre_topc(u1_struct_0(A_1051),u1_pre_topc(A_1051))),u1_struct_0(B_1052))
      | ~ m1_subset_1(D_1050,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1051),u1_struct_0(B_1052))))
      | ~ v1_funct_2(D_1050,u1_struct_0(A_1051),u1_struct_0(B_1052))
      | ~ v1_funct_1(D_1050)
      | ~ l1_pre_topc(B_1052)
      | ~ v2_pre_topc(B_1052)
      | ~ l1_pre_topc(A_1051)
      | ~ v2_pre_topc(A_1051) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_17140,plain,(
    ! [D_1050,B_1052] :
      ( v5_pre_topc(D_1050,'#skF_1',B_1052)
      | ~ v5_pre_topc(D_1050,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_1052)
      | ~ m1_subset_1(D_1050,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1'))),u1_struct_0(B_1052))))
      | ~ v1_funct_2(D_1050,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_1052))
      | ~ m1_subset_1(D_1050,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_1052))))
      | ~ v1_funct_2(D_1050,u1_struct_0('#skF_1'),u1_struct_0(B_1052))
      | ~ v1_funct_1(D_1050)
      | ~ l1_pre_topc(B_1052)
      | ~ v2_pre_topc(B_1052)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17029,c_17137])).

tff(c_17145,plain,(
    ! [D_1050,B_1052] :
      ( v5_pre_topc(D_1050,'#skF_1',B_1052)
      | ~ v5_pre_topc(D_1050,g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1')),B_1052)
      | ~ m1_subset_1(D_1050,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1'))),u1_struct_0(B_1052))))
      | ~ v1_funct_2(D_1050,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1'))),u1_struct_0(B_1052))
      | ~ m1_subset_1(D_1050,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(B_1052))))
      | ~ v1_funct_2(D_1050,k1_xboole_0,u1_struct_0(B_1052))
      | ~ v1_funct_1(D_1050)
      | ~ l1_pre_topc(B_1052)
      | ~ v2_pre_topc(B_1052) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_17029,c_17029,c_17029,c_17029,c_17140])).

tff(c_21498,plain,(
    ! [D_1191,B_1192] :
      ( v5_pre_topc(D_1191,'#skF_1',B_1192)
      | ~ v5_pre_topc(D_1191,g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),B_1192)
      | ~ m1_subset_1(D_1191,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),u1_struct_0(B_1192))))
      | ~ v1_funct_2(D_1191,u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),u1_struct_0(B_1192))
      | ~ m1_subset_1(D_1191,k1_zfmisc_1(k2_zfmisc_1('#skF_4',u1_struct_0(B_1192))))
      | ~ v1_funct_2(D_1191,'#skF_4',u1_struct_0(B_1192))
      | ~ v1_funct_1(D_1191)
      | ~ l1_pre_topc(B_1192)
      | ~ v2_pre_topc(B_1192) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20749,c_20749,c_20749,c_20749,c_20749,c_17145])).

tff(c_21508,plain,(
    ! [D_1191] :
      ( v5_pre_topc(D_1191,'#skF_1','#skF_1')
      | ~ v5_pre_topc(D_1191,g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),'#skF_1')
      | ~ m1_subset_1(D_1191,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),'#skF_4')))
      | ~ v1_funct_2(D_1191,u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),u1_struct_0('#skF_1'))
      | ~ m1_subset_1(D_1191,k1_zfmisc_1(k2_zfmisc_1('#skF_4',u1_struct_0('#skF_1'))))
      | ~ v1_funct_2(D_1191,'#skF_4',u1_struct_0('#skF_1'))
      | ~ v1_funct_1(D_1191)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20787,c_21498])).

tff(c_21621,plain,(
    ! [D_1203] :
      ( v5_pre_topc(D_1203,'#skF_1','#skF_1')
      | ~ v5_pre_topc(D_1203,g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),'#skF_1')
      | ~ m1_subset_1(D_1203,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),'#skF_4')))
      | ~ v1_funct_2(D_1203,u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),'#skF_4')
      | ~ m1_subset_1(D_1203,k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4')))
      | ~ v1_funct_2(D_1203,'#skF_4','#skF_4')
      | ~ v1_funct_1(D_1203) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_20787,c_20787,c_20787,c_21508])).

tff(c_21624,plain,
    ( v5_pre_topc('#skF_4','#skF_1','#skF_1')
    | ~ v5_pre_topc('#skF_4',g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),'#skF_1')
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),'#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4')))
    | ~ v1_funct_2('#skF_4','#skF_4','#skF_4')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20758,c_21621])).

tff(c_21631,plain,
    ( v5_pre_topc('#skF_4','#skF_1','#skF_1')
    | ~ v5_pre_topc('#skF_4',g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),'#skF_1')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_20764,c_20761,c_21624])).

tff(c_21635,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_21631])).

tff(c_21650,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_20759,c_21635])).

tff(c_21654,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_21650])).

tff(c_21656,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_21631])).

tff(c_17034,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17029,c_162])).

tff(c_20773,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20749,c_17034])).

tff(c_17363,plain,(
    ! [A_28] :
      ( v5_pre_topc('#skF_4',A_28,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_28),u1_pre_topc(A_28)),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_28),u1_pre_topc(A_28))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_28),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_28),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_28)
      | ~ v2_pre_topc(A_28)
      | ~ r1_tarski(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(A_28),u1_pre_topc(A_28)))) ) ),
    inference(resolution,[status(thm)],[c_17355,c_50])).

tff(c_17400,plain,(
    ! [A_28] :
      ( v5_pre_topc('#skF_4',A_28,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_28),u1_pre_topc(A_28)),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_28),u1_pre_topc(A_28))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_28),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_28),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_28)
      | ~ v2_pre_topc(A_28)
      | ~ r1_tarski(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(A_28),u1_pre_topc(A_28)))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_17363])).

tff(c_21300,plain,(
    ! [A_28] :
      ( v5_pre_topc('#skF_4',A_28,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_28),u1_pre_topc(A_28)),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_28),u1_pre_topc(A_28))),'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_28),'#skF_4')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_28),'#skF_4')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_28)
      | ~ v2_pre_topc(A_28)
      | ~ r1_tarski('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_28),u1_pre_topc(A_28)))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20749,c_20803,c_20803,c_20803,c_17400])).

tff(c_21301,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_21300])).

tff(c_21304,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_21301])).

tff(c_21308,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_21304])).

tff(c_21310,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_21300])).

tff(c_17440,plain,(
    ! [D_1063,A_1064,B_1065] :
      ( v5_pre_topc(D_1063,g1_pre_topc(u1_struct_0(A_1064),u1_pre_topc(A_1064)),B_1065)
      | ~ v5_pre_topc(D_1063,A_1064,B_1065)
      | ~ m1_subset_1(D_1063,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1064),u1_pre_topc(A_1064))),u1_struct_0(B_1065))))
      | ~ v1_funct_2(D_1063,u1_struct_0(g1_pre_topc(u1_struct_0(A_1064),u1_pre_topc(A_1064))),u1_struct_0(B_1065))
      | ~ m1_subset_1(D_1063,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1064),u1_struct_0(B_1065))))
      | ~ v1_funct_2(D_1063,u1_struct_0(A_1064),u1_struct_0(B_1065))
      | ~ v1_funct_1(D_1063)
      | ~ l1_pre_topc(B_1065)
      | ~ v2_pre_topc(B_1065)
      | ~ l1_pre_topc(A_1064)
      | ~ v2_pre_topc(A_1064) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_17444,plain,(
    ! [A_1064] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_1064),u1_pre_topc(A_1064)),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc('#skF_4',A_1064,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_1064),u1_pre_topc(A_1064))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1064),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1064),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_1064)
      | ~ v2_pre_topc(A_1064)
      | ~ r1_tarski(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(A_1064),u1_pre_topc(A_1064)))) ) ),
    inference(resolution,[status(thm)],[c_13834,c_17440])).

tff(c_17457,plain,(
    ! [A_1064] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_1064),u1_pre_topc(A_1064)),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc('#skF_4',A_1064,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_1064),u1_pre_topc(A_1064))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1064),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1064),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_1064)
      | ~ v2_pre_topc(A_1064)
      | ~ r1_tarski(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(A_1064),u1_pre_topc(A_1064)))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_17444])).

tff(c_21343,plain,(
    ! [A_1064] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_1064),u1_pre_topc(A_1064)),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc('#skF_4',A_1064,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_1064),u1_pre_topc(A_1064))),'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1064),'#skF_4')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1064),'#skF_4')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_1064)
      | ~ v2_pre_topc(A_1064)
      | ~ r1_tarski('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_1064),u1_pre_topc(A_1064)))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20749,c_21310,c_20803,c_20803,c_20803,c_17457])).

tff(c_21344,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_21343])).

tff(c_21347,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_120,c_21344])).

tff(c_21351,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_21347])).

tff(c_21353,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_21343])).

tff(c_21309,plain,(
    ! [A_28] :
      ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | v5_pre_topc('#skF_4',A_28,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_28),u1_pre_topc(A_28)),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_28),u1_pre_topc(A_28))),'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_28),'#skF_4')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_28),'#skF_4')
      | ~ l1_pre_topc(A_28)
      | ~ v2_pre_topc(A_28)
      | ~ r1_tarski('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_28),u1_pre_topc(A_28)))) ) ),
    inference(splitRight,[status(thm)],[c_21300])).

tff(c_21922,plain,(
    ! [A_1225] :
      ( v5_pre_topc('#skF_4',A_1225,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_1225),u1_pre_topc(A_1225)),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_1225),u1_pre_topc(A_1225))),'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1225),'#skF_4')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1225),'#skF_4')
      | ~ l1_pre_topc(A_1225)
      | ~ v2_pre_topc(A_1225)
      | ~ r1_tarski('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_1225),u1_pre_topc(A_1225)))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21353,c_21309])).

tff(c_21934,plain,
    ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4',g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),'#skF_4')))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ r1_tarski('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_20787,c_21922])).

tff(c_21941,plain,(
    v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20779,c_20787,c_78,c_76,c_20764,c_20787,c_21656,c_20787,c_20761,c_20787,c_20773,c_21934])).

tff(c_21943,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_21355,c_21941])).

tff(c_21945,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_20802])).

tff(c_22227,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20766,c_21945])).

tff(c_22228,plain,(
    u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1'))) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_17136])).

tff(c_17047,plain,
    ( v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_17029,c_46])).

tff(c_17060,plain,(
    v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_17047])).

tff(c_17053,plain,
    ( l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_17029,c_120])).

tff(c_17064,plain,(
    l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_17053])).

tff(c_22233,plain,(
    v1_funct_2('#skF_4',k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22228,c_17039])).

tff(c_22464,plain,(
    ! [D_1236,A_1237,B_1238] :
      ( v5_pre_topc(D_1236,A_1237,B_1238)
      | ~ v5_pre_topc(D_1236,A_1237,g1_pre_topc(u1_struct_0(B_1238),u1_pre_topc(B_1238)))
      | ~ m1_subset_1(D_1236,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1237),u1_struct_0(g1_pre_topc(u1_struct_0(B_1238),u1_pre_topc(B_1238))))))
      | ~ v1_funct_2(D_1236,u1_struct_0(A_1237),u1_struct_0(g1_pre_topc(u1_struct_0(B_1238),u1_pre_topc(B_1238))))
      | ~ m1_subset_1(D_1236,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1237),u1_struct_0(B_1238))))
      | ~ v1_funct_2(D_1236,u1_struct_0(A_1237),u1_struct_0(B_1238))
      | ~ v1_funct_1(D_1236)
      | ~ l1_pre_topc(B_1238)
      | ~ v2_pre_topc(B_1238)
      | ~ l1_pre_topc(A_1237)
      | ~ v2_pre_topc(A_1237) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_22468,plain,(
    ! [A_1237] :
      ( v5_pre_topc('#skF_4',A_1237,'#skF_2')
      | ~ v5_pre_topc('#skF_4',A_1237,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1237),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1237),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1237),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_1237)
      | ~ v2_pre_topc(A_1237)
      | ~ r1_tarski(k1_xboole_0,u1_struct_0(A_1237)) ) ),
    inference(resolution,[status(thm)],[c_13834,c_22464])).

tff(c_27088,plain,(
    ! [A_1385] :
      ( v5_pre_topc('#skF_4',A_1385,'#skF_2')
      | ~ v5_pre_topc('#skF_4',A_1385,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1385),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1385),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1385),u1_struct_0('#skF_2'))
      | ~ l1_pre_topc(A_1385)
      | ~ v2_pre_topc(A_1385)
      | ~ r1_tarski(k1_xboole_0,u1_struct_0(A_1385)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_64,c_22468])).

tff(c_27094,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1')),'#skF_2')
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v1_funct_2('#skF_4',k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2'))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1')))
    | ~ v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1')))
    | ~ r1_tarski(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_22228,c_27088])).

tff(c_27100,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_22228,c_17060,c_17064,c_17040,c_22228,c_17038,c_22228,c_22233,c_17034,c_27094])).

tff(c_17267,plain,(
    ! [B_1056] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_1056,u1_struct_0('#skF_2'))))
      | ~ r1_tarski(k1_xboole_0,B_1056) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13829,c_201])).

tff(c_17271,plain,(
    ! [A_28] :
      ( v5_pre_topc('#skF_4',A_28,'#skF_2')
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_28),u1_pre_topc(A_28)),'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_28),u1_pre_topc(A_28))),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_28),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_28),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_28)
      | ~ v2_pre_topc(A_28)
      | ~ r1_tarski(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(A_28),u1_pre_topc(A_28)))) ) ),
    inference(resolution,[status(thm)],[c_17267,c_50])).

tff(c_27200,plain,(
    ! [A_1393] :
      ( v5_pre_topc('#skF_4',A_1393,'#skF_2')
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_1393),u1_pre_topc(A_1393)),'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_1393),u1_pre_topc(A_1393))),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1393),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1393),u1_struct_0('#skF_2'))
      | ~ l1_pre_topc(A_1393)
      | ~ v2_pre_topc(A_1393)
      | ~ r1_tarski(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(A_1393),u1_pre_topc(A_1393)))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_64,c_17271])).

tff(c_27209,plain,
    ( v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ r1_tarski(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_17029,c_27200])).

tff(c_27214,plain,(
    v5_pre_topc('#skF_4','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_22228,c_17029,c_78,c_76,c_17040,c_17029,c_17038,c_17029,c_17040,c_22228,c_27100,c_17029,c_27209])).

tff(c_27216,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_194,c_27214])).

tff(c_27218,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_27441,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27439,c_27218])).

tff(c_27446,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27439,c_62])).

tff(c_27228,plain,(
    k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_27221])).

tff(c_27534,plain,(
    k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27439,c_27228])).

tff(c_27444,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27439,c_60])).

tff(c_27561,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0
    | k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') = u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(resolution,[status(thm)],[c_27444,c_32])).

tff(c_27583,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27446,c_27534,c_27561])).

tff(c_27596,plain,(
    u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_27583])).

tff(c_27453,plain,
    ( v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_27439,c_46])).

tff(c_27466,plain,(
    v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_27453])).

tff(c_27459,plain,
    ( l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_27439,c_120])).

tff(c_27470,plain,(
    l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_27459])).

tff(c_27447,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27439,c_87])).

tff(c_27445,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27439,c_91])).

tff(c_27600,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27596,c_27446])).

tff(c_27217,plain,(
    v5_pre_topc('#skF_4','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_30715,plain,(
    ! [D_1657,A_1658,B_1659] :
      ( v5_pre_topc(D_1657,g1_pre_topc(u1_struct_0(A_1658),u1_pre_topc(A_1658)),B_1659)
      | ~ v5_pre_topc(D_1657,A_1658,B_1659)
      | ~ m1_subset_1(D_1657,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1658),u1_pre_topc(A_1658))),u1_struct_0(B_1659))))
      | ~ v1_funct_2(D_1657,u1_struct_0(g1_pre_topc(u1_struct_0(A_1658),u1_pre_topc(A_1658))),u1_struct_0(B_1659))
      | ~ m1_subset_1(D_1657,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1658),u1_struct_0(B_1659))))
      | ~ v1_funct_2(D_1657,u1_struct_0(A_1658),u1_struct_0(B_1659))
      | ~ v1_funct_1(D_1657)
      | ~ l1_pre_topc(B_1659)
      | ~ v2_pre_topc(B_1659)
      | ~ l1_pre_topc(A_1658)
      | ~ v2_pre_topc(A_1658) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_30724,plain,(
    ! [D_1657,B_1659] :
      ( v5_pre_topc(D_1657,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_1659)
      | ~ v5_pre_topc(D_1657,'#skF_1',B_1659)
      | ~ m1_subset_1(D_1657,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(B_1659))))
      | ~ v1_funct_2(D_1657,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_1659))
      | ~ m1_subset_1(D_1657,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_1659))))
      | ~ v1_funct_2(D_1657,u1_struct_0('#skF_1'),u1_struct_0(B_1659))
      | ~ v1_funct_1(D_1657)
      | ~ l1_pre_topc(B_1659)
      | ~ v2_pre_topc(B_1659)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27439,c_30715])).

tff(c_30810,plain,(
    ! [D_1664,B_1665] :
      ( v5_pre_topc(D_1664,g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),B_1665)
      | ~ v5_pre_topc(D_1664,'#skF_1',B_1665)
      | ~ m1_subset_1(D_1664,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_1665))))
      | ~ v1_funct_2(D_1664,k1_relat_1('#skF_4'),u1_struct_0(B_1665))
      | ~ v1_funct_1(D_1664)
      | ~ l1_pre_topc(B_1665)
      | ~ v2_pre_topc(B_1665) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_27439,c_27439,c_27596,c_27439,c_27596,c_27439,c_30724])).

tff(c_30819,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_27445,c_30810])).

tff(c_30839,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_64,c_27447,c_27217,c_30819])).

tff(c_27256,plain,(
    ! [B_1408] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_1408,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_1408) ) ),
    inference(resolution,[status(thm)],[c_60,c_27251])).

tff(c_30849,plain,(
    ! [D_1666,A_1667,B_1668] :
      ( v5_pre_topc(D_1666,A_1667,g1_pre_topc(u1_struct_0(B_1668),u1_pre_topc(B_1668)))
      | ~ v5_pre_topc(D_1666,A_1667,B_1668)
      | ~ m1_subset_1(D_1666,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1667),u1_struct_0(g1_pre_topc(u1_struct_0(B_1668),u1_pre_topc(B_1668))))))
      | ~ v1_funct_2(D_1666,u1_struct_0(A_1667),u1_struct_0(g1_pre_topc(u1_struct_0(B_1668),u1_pre_topc(B_1668))))
      | ~ m1_subset_1(D_1666,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1667),u1_struct_0(B_1668))))
      | ~ v1_funct_2(D_1666,u1_struct_0(A_1667),u1_struct_0(B_1668))
      | ~ v1_funct_1(D_1666)
      | ~ l1_pre_topc(B_1668)
      | ~ v2_pre_topc(B_1668)
      | ~ l1_pre_topc(A_1667)
      | ~ v2_pre_topc(A_1667) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_30865,plain,(
    ! [A_1667] :
      ( v5_pre_topc('#skF_4',A_1667,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc('#skF_4',A_1667,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1667),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1667),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1667),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_1667)
      | ~ v2_pre_topc(A_1667)
      | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(A_1667)) ) ),
    inference(resolution,[status(thm)],[c_27256,c_30849])).

tff(c_30879,plain,(
    ! [A_1669] :
      ( v5_pre_topc('#skF_4',A_1669,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc('#skF_4',A_1669,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1669),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1669),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1669),u1_struct_0('#skF_2'))
      | ~ l1_pre_topc(A_1669)
      | ~ v2_pre_topc(A_1669)
      | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(A_1669)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_64,c_30865])).

tff(c_30885,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2'))
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))
    | ~ v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))
    | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_27596,c_30879])).

tff(c_30891,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_27596,c_27466,c_27470,c_27447,c_27596,c_27445,c_27596,c_27600,c_30839,c_30885])).

tff(c_30893,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_27441,c_30891])).

tff(c_30894,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_27583])).

tff(c_30899,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30894,c_27446])).

tff(c_30896,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30894,c_27444])).

tff(c_31041,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),k1_xboole_0)
    | u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30896,c_24])).

tff(c_31067,plain,
    ( k1_xboole_0 = '#skF_4'
    | u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30899,c_31041])).

tff(c_31075,plain,(
    u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_31067])).

tff(c_27442,plain,(
    v4_relat_1('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27439,c_143])).

tff(c_31079,plain,(
    v4_relat_1('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31075,c_27442])).

tff(c_31081,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_27416,c_31079])).

tff(c_31082,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_31067])).

tff(c_30900,plain,(
    ! [B_1408] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_1408,k1_xboole_0)))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_1408) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30894,c_27256])).

tff(c_31088,plain,(
    ! [B_1408] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_1408,'#skF_4')))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_1408) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31082,c_30900])).

tff(c_31306,plain,(
    ! [A_1685] :
      ( v1_funct_2('#skF_4',A_1685,'#skF_4')
      | A_1685 = '#skF_4'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_1685,'#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31082,c_31082,c_31082,c_31082,c_31082,c_22])).

tff(c_31341,plain,(
    ! [B_1689] :
      ( v1_funct_2('#skF_4',B_1689,'#skF_4')
      | B_1689 = '#skF_4'
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_1689) ) ),
    inference(resolution,[status(thm)],[c_31088,c_31306])).

tff(c_31353,plain,
    ( v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_4')
    | k1_relat_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6,c_31341])).

tff(c_31354,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_31353])).

tff(c_31095,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31082,c_27410])).

tff(c_31364,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31354,c_31095])).

tff(c_31384,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_31364])).

tff(c_31385,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_31353])).

tff(c_30970,plain,(
    ! [D_1671,A_1672,B_1673] :
      ( v5_pre_topc(D_1671,A_1672,g1_pre_topc(u1_struct_0(B_1673),u1_pre_topc(B_1673)))
      | ~ v5_pre_topc(D_1671,A_1672,B_1673)
      | ~ m1_subset_1(D_1671,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1672),u1_struct_0(g1_pre_topc(u1_struct_0(B_1673),u1_pre_topc(B_1673))))))
      | ~ v1_funct_2(D_1671,u1_struct_0(A_1672),u1_struct_0(g1_pre_topc(u1_struct_0(B_1673),u1_pre_topc(B_1673))))
      | ~ m1_subset_1(D_1671,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1672),u1_struct_0(B_1673))))
      | ~ v1_funct_2(D_1671,u1_struct_0(A_1672),u1_struct_0(B_1673))
      | ~ v1_funct_1(D_1671)
      | ~ l1_pre_topc(B_1673)
      | ~ v2_pre_topc(B_1673)
      | ~ l1_pre_topc(A_1672)
      | ~ v2_pre_topc(A_1672) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_30979,plain,(
    ! [D_1671,A_1672] :
      ( v5_pre_topc(D_1671,A_1672,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc(D_1671,A_1672,'#skF_2')
      | ~ m1_subset_1(D_1671,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1672),k1_xboole_0)))
      | ~ v1_funct_2(D_1671,u1_struct_0(A_1672),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1(D_1671,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1672),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_1671,u1_struct_0(A_1672),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_1671)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_1672)
      | ~ v2_pre_topc(A_1672) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30894,c_30970])).

tff(c_30989,plain,(
    ! [D_1671,A_1672] :
      ( v5_pre_topc(D_1671,A_1672,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc(D_1671,A_1672,'#skF_2')
      | ~ m1_subset_1(D_1671,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1672),k1_xboole_0)))
      | ~ v1_funct_2(D_1671,u1_struct_0(A_1672),k1_xboole_0)
      | ~ m1_subset_1(D_1671,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1672),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_1671,u1_struct_0(A_1672),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_1671)
      | ~ l1_pre_topc(A_1672)
      | ~ v2_pre_topc(A_1672) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_30894,c_30979])).

tff(c_31965,plain,(
    ! [D_1722,A_1723] :
      ( v5_pre_topc(D_1722,A_1723,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc(D_1722,A_1723,'#skF_2')
      | ~ m1_subset_1(D_1722,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1723),'#skF_4')))
      | ~ v1_funct_2(D_1722,u1_struct_0(A_1723),'#skF_4')
      | ~ m1_subset_1(D_1722,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1723),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_1722,u1_struct_0(A_1723),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_1722)
      | ~ l1_pre_topc(A_1723)
      | ~ v2_pre_topc(A_1723) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31082,c_31082,c_30989])).

tff(c_31971,plain,(
    ! [D_1722] :
      ( v5_pre_topc(D_1722,'#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc(D_1722,'#skF_1','#skF_2')
      | ~ m1_subset_1(D_1722,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),'#skF_4')))
      | ~ v1_funct_2(D_1722,u1_struct_0('#skF_1'),'#skF_4')
      | ~ m1_subset_1(D_1722,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_1722,u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_1722)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27439,c_31965])).

tff(c_32099,plain,(
    ! [D_1727] :
      ( v5_pre_topc(D_1727,'#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc(D_1727,'#skF_1','#skF_2')
      | ~ m1_subset_1(D_1727,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_4')))
      | ~ v1_funct_2(D_1727,k1_relat_1('#skF_4'),'#skF_4')
      | ~ m1_subset_1(D_1727,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_1727,k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_1727) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_27439,c_27439,c_27439,c_31971])).

tff(c_32102,plain,
    ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_4')))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_4')
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_27445,c_32099])).

tff(c_32109,plain,
    ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_27447,c_31385,c_27217,c_32102])).

tff(c_32113,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_32109])).

tff(c_32127,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_31088,c_32113])).

tff(c_32131,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_32127])).

tff(c_32133,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_32109])).

tff(c_31089,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31082,c_30899])).

tff(c_31084,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),'#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31082,c_30896])).

tff(c_32132,plain,(
    v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_32109])).

tff(c_30908,plain,
    ( v1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_30894,c_149])).

tff(c_31432,plain,
    ( v1_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31082,c_30908])).

tff(c_31433,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_31432])).

tff(c_31437,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_120,c_31433])).

tff(c_31441,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_31437])).

tff(c_31443,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_31432])).

tff(c_30905,plain,
    ( v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_30894,c_46])).

tff(c_31949,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31443,c_31082,c_30905])).

tff(c_31950,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_31949])).

tff(c_31954,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_31950])).

tff(c_31958,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_31954])).

tff(c_31960,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_31949])).

tff(c_31091,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31082,c_30894])).

tff(c_31208,plain,(
    ! [D_1681,A_1682,B_1683] :
      ( v5_pre_topc(D_1681,g1_pre_topc(u1_struct_0(A_1682),u1_pre_topc(A_1682)),B_1683)
      | ~ v5_pre_topc(D_1681,A_1682,B_1683)
      | ~ m1_subset_1(D_1681,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1682),u1_pre_topc(A_1682))),u1_struct_0(B_1683))))
      | ~ v1_funct_2(D_1681,u1_struct_0(g1_pre_topc(u1_struct_0(A_1682),u1_pre_topc(A_1682))),u1_struct_0(B_1683))
      | ~ m1_subset_1(D_1681,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1682),u1_struct_0(B_1683))))
      | ~ v1_funct_2(D_1681,u1_struct_0(A_1682),u1_struct_0(B_1683))
      | ~ v1_funct_1(D_1681)
      | ~ l1_pre_topc(B_1683)
      | ~ v2_pre_topc(B_1683)
      | ~ l1_pre_topc(A_1682)
      | ~ v2_pre_topc(A_1682) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_31220,plain,(
    ! [D_1681,B_1683] :
      ( v5_pre_topc(D_1681,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_1683)
      | ~ v5_pre_topc(D_1681,'#skF_1',B_1683)
      | ~ m1_subset_1(D_1681,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(B_1683))))
      | ~ v1_funct_2(D_1681,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_1683))
      | ~ m1_subset_1(D_1681,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_1683))))
      | ~ v1_funct_2(D_1681,u1_struct_0('#skF_1'),u1_struct_0(B_1683))
      | ~ v1_funct_1(D_1681)
      | ~ l1_pre_topc(B_1683)
      | ~ v2_pre_topc(B_1683)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27439,c_31208])).

tff(c_32487,plain,(
    ! [D_1766,B_1767] :
      ( v5_pre_topc(D_1766,g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),B_1767)
      | ~ v5_pre_topc(D_1766,'#skF_1',B_1767)
      | ~ m1_subset_1(D_1766,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(B_1767))))
      | ~ v1_funct_2(D_1766,u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(B_1767))
      | ~ m1_subset_1(D_1766,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_1767))))
      | ~ v1_funct_2(D_1766,k1_relat_1('#skF_4'),u1_struct_0(B_1767))
      | ~ v1_funct_1(D_1766)
      | ~ l1_pre_topc(B_1767)
      | ~ v2_pre_topc(B_1767) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_27439,c_27439,c_27439,c_27439,c_31220])).

tff(c_32490,plain,(
    ! [D_1766] :
      ( v5_pre_topc(D_1766,g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc(D_1766,'#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ m1_subset_1(D_1766,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),'#skF_4')))
      | ~ v1_funct_2(D_1766,u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1(D_1766,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))))
      | ~ v1_funct_2(D_1766,k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ v1_funct_1(D_1766)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31091,c_32487])).

tff(c_32586,plain,(
    ! [D_1774] :
      ( v5_pre_topc(D_1774,g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc(D_1774,'#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ m1_subset_1(D_1774,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),'#skF_4')))
      | ~ v1_funct_2(D_1774,u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),'#skF_4')
      | ~ m1_subset_1(D_1774,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_4')))
      | ~ v1_funct_2(D_1774,k1_relat_1('#skF_4'),'#skF_4')
      | ~ v1_funct_1(D_1774) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31960,c_31443,c_31091,c_31091,c_31091,c_32490])).

tff(c_32596,plain,
    ( ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),'#skF_4')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),'#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_4')))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_4')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32586,c_27441])).

tff(c_32604,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_31385,c_32133,c_31089,c_31084,c_32132,c_32596])).

tff(c_32605,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_27438])).

tff(c_32620,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32605,c_87])).

tff(c_32618,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32605,c_91])).

tff(c_32711,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),k1_xboole_0)
    | u1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32618,c_24])).

tff(c_32737,plain,
    ( k1_xboole_0 = '#skF_4'
    | u1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32620,c_32711])).

tff(c_32746,plain,(
    u1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_32737])).

tff(c_32754,plain,(
    v4_relat_1('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32746,c_144])).

tff(c_32756,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_27416,c_32754])).

tff(c_32757,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_32737])).

tff(c_32768,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32757,c_32620])).

tff(c_32759,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),'#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32757,c_32618])).

tff(c_27257,plain,(
    ! [B_1408] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_1408,u1_struct_0('#skF_2'))))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_1408) ) ),
    inference(resolution,[status(thm)],[c_91,c_27251])).

tff(c_32612,plain,(
    ! [B_1408] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_1408,k1_xboole_0)))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_1408) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32605,c_27257])).

tff(c_32929,plain,(
    ! [B_1408] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_1408,'#skF_4')))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_1408) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32757,c_32612])).

tff(c_33033,plain,(
    ! [A_1794] :
      ( v1_funct_2('#skF_4',A_1794,'#skF_4')
      | A_1794 = '#skF_4'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_1794,'#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32757,c_32757,c_32757,c_32757,c_32757,c_22])).

tff(c_33044,plain,(
    ! [B_1795] :
      ( v1_funct_2('#skF_4',B_1795,'#skF_4')
      | B_1795 = '#skF_4'
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_1795) ) ),
    inference(resolution,[status(thm)],[c_32929,c_33033])).

tff(c_33056,plain,
    ( v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_4')
    | k1_relat_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6,c_33044])).

tff(c_33057,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_33056])).

tff(c_32774,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32757,c_27410])).

tff(c_33066,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33057,c_32774])).

tff(c_33073,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_33066])).

tff(c_33074,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_33056])).

tff(c_32614,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32605,c_27218])).

tff(c_32985,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32757,c_32614])).

tff(c_32771,plain,(
    u1_struct_0('#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32757,c_32605])).

tff(c_32819,plain,(
    k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))),'#skF_4') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32771,c_27228])).

tff(c_27427,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0
    | k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') = u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(resolution,[status(thm)],[c_60,c_27418])).

tff(c_27435,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0
    | k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') = u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_27427])).

tff(c_33076,plain,
    ( u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) = '#skF_4'
    | u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32819,c_32771,c_32757,c_32771,c_27435])).

tff(c_33077,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_33076])).

tff(c_33126,plain,
    ( v1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_33077,c_149])).

tff(c_33276,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_33126])).

tff(c_33299,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_120,c_33276])).

tff(c_33303,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_33299])).

tff(c_33305,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_33126])).

tff(c_33123,plain,
    ( v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_33077,c_46])).

tff(c_33369,plain,
    ( v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33305,c_33123])).

tff(c_33370,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_33369])).

tff(c_33373,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_33370])).

tff(c_33377,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_33373])).

tff(c_33379,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_33369])).

tff(c_32619,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32605,c_62])).

tff(c_32770,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32757,c_32619])).

tff(c_33079,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33077,c_32770])).

tff(c_32609,plain,(
    ! [B_1408] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_1408,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2'))))))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_1408) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32605,c_27256])).

tff(c_32990,plain,(
    ! [B_1408] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_1408,u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_1408) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32757,c_32609])).

tff(c_32974,plain,(
    ! [D_1790,A_1791,B_1792] :
      ( v5_pre_topc(D_1790,A_1791,g1_pre_topc(u1_struct_0(B_1792),u1_pre_topc(B_1792)))
      | ~ v5_pre_topc(D_1790,A_1791,B_1792)
      | ~ m1_subset_1(D_1790,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1791),u1_struct_0(g1_pre_topc(u1_struct_0(B_1792),u1_pre_topc(B_1792))))))
      | ~ v1_funct_2(D_1790,u1_struct_0(A_1791),u1_struct_0(g1_pre_topc(u1_struct_0(B_1792),u1_pre_topc(B_1792))))
      | ~ m1_subset_1(D_1790,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1791),u1_struct_0(B_1792))))
      | ~ v1_funct_2(D_1790,u1_struct_0(A_1791),u1_struct_0(B_1792))
      | ~ v1_funct_1(D_1790)
      | ~ l1_pre_topc(B_1792)
      | ~ v2_pre_topc(B_1792)
      | ~ l1_pre_topc(A_1791)
      | ~ v2_pre_topc(A_1791) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_32980,plain,(
    ! [D_1790,A_1791] :
      ( v5_pre_topc(D_1790,A_1791,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc(D_1790,A_1791,'#skF_2')
      | ~ m1_subset_1(D_1790,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1791),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))))
      | ~ v1_funct_2(D_1790,u1_struct_0(A_1791),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1(D_1790,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1791),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_1790,u1_struct_0(A_1791),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_1790)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_1791)
      | ~ v2_pre_topc(A_1791) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32771,c_32974])).

tff(c_34041,plain,(
    ! [D_1871,A_1872] :
      ( v5_pre_topc(D_1871,A_1872,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc(D_1871,A_1872,'#skF_2')
      | ~ m1_subset_1(D_1871,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1872),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))))
      | ~ v1_funct_2(D_1871,u1_struct_0(A_1872),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1(D_1871,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1872),'#skF_4')))
      | ~ v1_funct_2(D_1871,u1_struct_0(A_1872),'#skF_4')
      | ~ v1_funct_1(D_1871)
      | ~ l1_pre_topc(A_1872)
      | ~ v2_pre_topc(A_1872) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_32771,c_32771,c_32771,c_32771,c_32980])).

tff(c_34048,plain,(
    ! [A_1872] :
      ( v5_pre_topc('#skF_4',A_1872,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc('#skF_4',A_1872,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1872),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1872),'#skF_4')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1872),'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(A_1872)
      | ~ v2_pre_topc(A_1872)
      | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(A_1872)) ) ),
    inference(resolution,[status(thm)],[c_32990,c_34041])).

tff(c_34077,plain,(
    ! [A_1875] :
      ( v5_pre_topc('#skF_4',A_1875,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc('#skF_4',A_1875,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1875),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1875),'#skF_4')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1875),'#skF_4')
      | ~ l1_pre_topc(A_1875)
      | ~ v2_pre_topc(A_1875)
      | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(A_1875)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_34048])).

tff(c_34083,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_33077,c_34077])).

tff(c_34089,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_33077,c_33379,c_33305,c_33074,c_33077,c_33077,c_33079,c_34083])).

tff(c_34090,plain,
    ( ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_32985,c_34089])).

tff(c_34093,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_34090])).

tff(c_34096,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_32929,c_34093])).

tff(c_34100,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_34096])).

tff(c_34102,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_34090])).

tff(c_52,plain,(
    ! [D_42,A_28,B_36] :
      ( v5_pre_topc(D_42,g1_pre_topc(u1_struct_0(A_28),u1_pre_topc(A_28)),B_36)
      | ~ v5_pre_topc(D_42,A_28,B_36)
      | ~ m1_subset_1(D_42,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_28),u1_pre_topc(A_28))),u1_struct_0(B_36))))
      | ~ v1_funct_2(D_42,u1_struct_0(g1_pre_topc(u1_struct_0(A_28),u1_pre_topc(A_28))),u1_struct_0(B_36))
      | ~ m1_subset_1(D_42,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_28),u1_struct_0(B_36))))
      | ~ v1_funct_2(D_42,u1_struct_0(A_28),u1_struct_0(B_36))
      | ~ v1_funct_1(D_42)
      | ~ l1_pre_topc(B_36)
      | ~ v2_pre_topc(B_36)
      | ~ l1_pre_topc(A_28)
      | ~ v2_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_33117,plain,(
    ! [D_42,B_36] :
      ( v5_pre_topc(D_42,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_36)
      | ~ v5_pre_topc(D_42,'#skF_1',B_36)
      | ~ m1_subset_1(D_42,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_36))))
      | ~ v1_funct_2(D_42,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_36))
      | ~ m1_subset_1(D_42,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_36))))
      | ~ v1_funct_2(D_42,u1_struct_0('#skF_1'),u1_struct_0(B_36))
      | ~ v1_funct_1(D_42)
      | ~ l1_pre_topc(B_36)
      | ~ v2_pre_topc(B_36)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33077,c_52])).

tff(c_33979,plain,(
    ! [D_1866,B_1867] :
      ( v5_pre_topc(D_1866,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_1867)
      | ~ v5_pre_topc(D_1866,'#skF_1',B_1867)
      | ~ m1_subset_1(D_1866,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_1867))))
      | ~ v1_funct_2(D_1866,k1_relat_1('#skF_4'),u1_struct_0(B_1867))
      | ~ m1_subset_1(D_1866,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_1867))))
      | ~ v1_funct_2(D_1866,u1_struct_0('#skF_1'),u1_struct_0(B_1867))
      | ~ v1_funct_1(D_1866)
      | ~ l1_pre_topc(B_1867)
      | ~ v2_pre_topc(B_1867) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_33077,c_33117])).

tff(c_33989,plain,(
    ! [D_1866] :
      ( v5_pre_topc(D_1866,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
      | ~ v5_pre_topc(D_1866,'#skF_1','#skF_2')
      | ~ m1_subset_1(D_1866,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_1866,k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(D_1866,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),'#skF_4')))
      | ~ v1_funct_2(D_1866,u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_1866)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32771,c_33979])).

tff(c_33997,plain,(
    ! [D_1866] :
      ( v5_pre_topc(D_1866,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
      | ~ v5_pre_topc(D_1866,'#skF_1','#skF_2')
      | ~ m1_subset_1(D_1866,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_4')))
      | ~ v1_funct_2(D_1866,k1_relat_1('#skF_4'),'#skF_4')
      | ~ m1_subset_1(D_1866,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),'#skF_4')))
      | ~ v1_funct_2(D_1866,u1_struct_0('#skF_1'),'#skF_4')
      | ~ v1_funct_1(D_1866) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_32771,c_32771,c_32771,c_33989])).

tff(c_34101,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_34090])).

tff(c_34169,plain,
    ( ~ v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_4')))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),'#skF_4')))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_33997,c_34101])).

tff(c_34173,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_32768,c_32759,c_33074,c_34102,c_27217,c_34169])).

tff(c_34174,plain,(
    u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_33076])).

tff(c_34177,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34174,c_32770])).

tff(c_32984,plain,(
    ! [D_1790,A_1791] :
      ( v5_pre_topc(D_1790,A_1791,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc(D_1790,A_1791,'#skF_2')
      | ~ m1_subset_1(D_1790,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1791),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))))
      | ~ v1_funct_2(D_1790,u1_struct_0(A_1791),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1(D_1790,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1791),'#skF_4')))
      | ~ v1_funct_2(D_1790,u1_struct_0(A_1791),'#skF_4')
      | ~ v1_funct_1(D_1790)
      | ~ l1_pre_topc(A_1791)
      | ~ v2_pre_topc(A_1791) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_32771,c_32771,c_32771,c_32771,c_32980])).

tff(c_34416,plain,(
    ! [D_1897,A_1898] :
      ( v5_pre_topc(D_1897,A_1898,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc(D_1897,A_1898,'#skF_2')
      | ~ m1_subset_1(D_1897,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1898),'#skF_4')))
      | ~ v1_funct_2(D_1897,u1_struct_0(A_1898),'#skF_4')
      | ~ m1_subset_1(D_1897,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1898),'#skF_4')))
      | ~ v1_funct_2(D_1897,u1_struct_0(A_1898),'#skF_4')
      | ~ v1_funct_1(D_1897)
      | ~ l1_pre_topc(A_1898)
      | ~ v2_pre_topc(A_1898) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34174,c_34174,c_32984])).

tff(c_34425,plain,
    ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),'#skF_4')))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32759,c_34416])).

tff(c_34439,plain,(
    v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_64,c_32768,c_32759,c_27217,c_34425])).

tff(c_32624,plain,
    ( v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_32605,c_46])).

tff(c_32637,plain,(
    v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_32624])).

tff(c_32767,plain,(
    v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32757,c_32637])).

tff(c_32630,plain,
    ( l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_32605,c_120])).

tff(c_32641,plain,(
    l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_32630])).

tff(c_32766,plain,(
    l1_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32757,c_32641])).

tff(c_32991,plain,(
    ! [B_1793] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_1793,u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_1793) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32757,c_32609])).

tff(c_32999,plain,(
    ! [A_28] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_28),u1_pre_topc(A_28)),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc('#skF_4',A_28,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_28),u1_pre_topc(A_28))),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_28),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_28),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_28)
      | ~ v2_pre_topc(A_28)
      | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0(A_28),u1_pre_topc(A_28)))) ) ),
    inference(resolution,[status(thm)],[c_32991,c_52])).

tff(c_33022,plain,(
    ! [A_28] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_28),u1_pre_topc(A_28)),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc('#skF_4',A_28,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_28),u1_pre_topc(A_28))),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_28),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_28),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
      | ~ l1_pre_topc(A_28)
      | ~ v2_pre_topc(A_28)
      | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0(A_28),u1_pre_topc(A_28)))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32767,c_32766,c_64,c_32999])).

tff(c_34658,plain,(
    ! [A_1915] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_1915),u1_pre_topc(A_1915)),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc('#skF_4',A_1915,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_1915),u1_pre_topc(A_1915))),'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1915),'#skF_4')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1915),'#skF_4')
      | ~ l1_pre_topc(A_1915)
      | ~ v2_pre_topc(A_1915)
      | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0(A_1915),u1_pre_topc(A_1915)))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34174,c_34174,c_34174,c_33022])).

tff(c_34667,plain,
    ( ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),'#skF_4')))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(resolution,[status(thm)],[c_34658,c_32985])).

tff(c_34678,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_32768,c_32759,c_34177,c_34439,c_34667])).

tff(c_34685,plain,
    ( ~ v4_relat_1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_34678])).

tff(c_34689,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_143,c_34685])).

tff(c_34691,plain,(
    r1_tarski(k1_relat_1('#skF_4'),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_27282])).

tff(c_27284,plain,(
    ! [B_1411] :
      ( k1_relset_1(B_1411,u1_struct_0('#skF_2'),'#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_1411) ) ),
    inference(resolution,[status(thm)],[c_27258,c_18])).

tff(c_34703,plain,(
    k1_relset_1(k1_xboole_0,u1_struct_0('#skF_2'),'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34691,c_27284])).

tff(c_27303,plain,(
    ! [C_1413,A_1414,B_1415] :
      ( v1_funct_2(C_1413,A_1414,B_1415)
      | k1_relset_1(A_1414,B_1415,C_1413) != A_1414
      | ~ m1_subset_1(C_1413,k1_zfmisc_1(k2_zfmisc_1(A_1414,B_1415)))
      | ~ v1_funct_1(C_1413) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_27306,plain,(
    ! [B_1408] :
      ( v1_funct_2('#skF_4',B_1408,u1_struct_0('#skF_2'))
      | k1_relset_1(B_1408,u1_struct_0('#skF_2'),'#skF_4') != B_1408
      | ~ v1_funct_1('#skF_4')
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_1408) ) ),
    inference(resolution,[status(thm)],[c_27257,c_27303])).

tff(c_34850,plain,(
    ! [B_1922] :
      ( v1_funct_2('#skF_4',B_1922,u1_struct_0('#skF_2'))
      | k1_relset_1(B_1922,u1_struct_0('#skF_2'),'#skF_4') != B_1922
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_1922) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_27306])).

tff(c_34690,plain,
    ( ~ v1_funct_2('#skF_4',k1_xboole_0,u1_struct_0('#skF_2'))
    | k1_relset_1(k1_xboole_0,u1_struct_0('#skF_2'),'#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_27282])).

tff(c_34848,plain,
    ( ~ v1_funct_2('#skF_4',k1_xboole_0,u1_struct_0('#skF_2'))
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34703,c_34690])).

tff(c_34849,plain,(
    ~ v1_funct_2('#skF_4',k1_xboole_0,u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_34848])).

tff(c_34853,plain,
    ( k1_relset_1(k1_xboole_0,u1_struct_0('#skF_2'),'#skF_4') != k1_xboole_0
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_34850,c_34849])).

tff(c_34856,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34691,c_34703,c_34853])).

tff(c_34726,plain,(
    ! [B_1916,A_1917,C_1918] :
      ( k1_xboole_0 = B_1916
      | k1_relset_1(A_1917,B_1916,C_1918) = A_1917
      | ~ v1_funct_2(C_1918,A_1917,B_1916)
      | ~ m1_subset_1(C_1918,k1_zfmisc_1(k2_zfmisc_1(A_1917,B_1916))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_34738,plain,
    ( u1_struct_0('#skF_2') = k1_xboole_0
    | k1_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4') = u1_struct_0('#skF_1')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_91,c_34726])).

tff(c_34746,plain,
    ( u1_struct_0('#skF_2') = k1_xboole_0
    | u1_struct_0('#skF_1') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_27229,c_34738])).

tff(c_34747,plain,(
    u1_struct_0('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_34746])).

tff(c_34749,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34747,c_27218])).

tff(c_34754,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34747,c_62])).

tff(c_34843,plain,(
    k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34747,c_27228])).

tff(c_34752,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34747,c_60])).

tff(c_34907,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0
    | k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') = u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(resolution,[status(thm)],[c_34752,c_32])).

tff(c_34929,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34754,c_34843,c_34907])).

tff(c_34945,plain,(
    u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_34929])).

tff(c_34761,plain,
    ( v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_34747,c_46])).

tff(c_34774,plain,(
    v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_34761])).

tff(c_34767,plain,
    ( l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_34747,c_120])).

tff(c_34778,plain,(
    l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_34767])).

tff(c_34755,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34747,c_87])).

tff(c_34753,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34747,c_91])).

tff(c_34949,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34945,c_34754])).

tff(c_37435,plain,(
    ! [D_2051,A_2052,B_2053] :
      ( v5_pre_topc(D_2051,g1_pre_topc(u1_struct_0(A_2052),u1_pre_topc(A_2052)),B_2053)
      | ~ v5_pre_topc(D_2051,A_2052,B_2053)
      | ~ m1_subset_1(D_2051,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2052),u1_pre_topc(A_2052))),u1_struct_0(B_2053))))
      | ~ v1_funct_2(D_2051,u1_struct_0(g1_pre_topc(u1_struct_0(A_2052),u1_pre_topc(A_2052))),u1_struct_0(B_2053))
      | ~ m1_subset_1(D_2051,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2052),u1_struct_0(B_2053))))
      | ~ v1_funct_2(D_2051,u1_struct_0(A_2052),u1_struct_0(B_2053))
      | ~ v1_funct_1(D_2051)
      | ~ l1_pre_topc(B_2053)
      | ~ v2_pre_topc(B_2053)
      | ~ l1_pre_topc(A_2052)
      | ~ v2_pre_topc(A_2052) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_37444,plain,(
    ! [D_2051,B_2053] :
      ( v5_pre_topc(D_2051,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_2053)
      | ~ v5_pre_topc(D_2051,'#skF_1',B_2053)
      | ~ m1_subset_1(D_2051,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(B_2053))))
      | ~ v1_funct_2(D_2051,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_2053))
      | ~ m1_subset_1(D_2051,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_2053))))
      | ~ v1_funct_2(D_2051,u1_struct_0('#skF_1'),u1_struct_0(B_2053))
      | ~ v1_funct_1(D_2051)
      | ~ l1_pre_topc(B_2053)
      | ~ v2_pre_topc(B_2053)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34747,c_37435])).

tff(c_37471,plain,(
    ! [D_2055,B_2056] :
      ( v5_pre_topc(D_2055,g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),B_2056)
      | ~ v5_pre_topc(D_2055,'#skF_1',B_2056)
      | ~ m1_subset_1(D_2055,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_2056))))
      | ~ v1_funct_2(D_2055,k1_relat_1('#skF_4'),u1_struct_0(B_2056))
      | ~ v1_funct_1(D_2055)
      | ~ l1_pre_topc(B_2056)
      | ~ v2_pre_topc(B_2056) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_34747,c_34747,c_34945,c_34747,c_34945,c_34747,c_37444])).

tff(c_37480,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34753,c_37471])).

tff(c_37500,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_64,c_34755,c_27217,c_37480])).

tff(c_34985,plain,(
    ! [D_1927,A_1928,B_1929] :
      ( v5_pre_topc(D_1927,A_1928,g1_pre_topc(u1_struct_0(B_1929),u1_pre_topc(B_1929)))
      | ~ v5_pre_topc(D_1927,A_1928,B_1929)
      | ~ m1_subset_1(D_1927,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1928),u1_struct_0(g1_pre_topc(u1_struct_0(B_1929),u1_pre_topc(B_1929))))))
      | ~ v1_funct_2(D_1927,u1_struct_0(A_1928),u1_struct_0(g1_pre_topc(u1_struct_0(B_1929),u1_pre_topc(B_1929))))
      | ~ m1_subset_1(D_1927,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1928),u1_struct_0(B_1929))))
      | ~ v1_funct_2(D_1927,u1_struct_0(A_1928),u1_struct_0(B_1929))
      | ~ v1_funct_1(D_1927)
      | ~ l1_pre_topc(B_1929)
      | ~ v2_pre_topc(B_1929)
      | ~ l1_pre_topc(A_1928)
      | ~ v2_pre_topc(A_1928) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_35001,plain,(
    ! [A_1928] :
      ( v5_pre_topc('#skF_4',A_1928,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc('#skF_4',A_1928,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1928),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1928),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1928),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_1928)
      | ~ v2_pre_topc(A_1928)
      | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(A_1928)) ) ),
    inference(resolution,[status(thm)],[c_27256,c_34985])).

tff(c_37510,plain,(
    ! [A_2057] :
      ( v5_pre_topc('#skF_4',A_2057,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc('#skF_4',A_2057,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_2057),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2057),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_2057),u1_struct_0('#skF_2'))
      | ~ l1_pre_topc(A_2057)
      | ~ v2_pre_topc(A_2057)
      | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(A_2057)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_64,c_35001])).

tff(c_37516,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2'))
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))
    | ~ v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))
    | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_34945,c_37510])).

tff(c_37522,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_34945,c_34774,c_34778,c_34755,c_34945,c_34753,c_34945,c_34949,c_37500,c_37516])).

tff(c_37524,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34749,c_37522])).

tff(c_37525,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_34929])).

tff(c_27339,plain,(
    ! [B_1417] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_1417,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_1417) ) ),
    inference(resolution,[status(thm)],[c_60,c_27251])).

tff(c_27369,plain,
    ( k1_relset_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_4',k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_27339,c_30])).

tff(c_34943,plain,
    ( k1_relset_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_4',k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34691,c_27369])).

tff(c_34944,plain,(
    ~ v1_funct_2('#skF_4',k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_34943])).

tff(c_37527,plain,(
    ~ v1_funct_2('#skF_4',k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37525,c_34944])).

tff(c_37531,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37525,c_34754])).

tff(c_37528,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37525,c_34752])).

tff(c_37712,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),k1_xboole_0)
    | u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_37528,c_24])).

tff(c_37738,plain,
    ( k1_xboole_0 = '#skF_4'
    | u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_37531,c_37712])).

tff(c_37746,plain,(
    u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_37738])).

tff(c_37748,plain,(
    v1_funct_2('#skF_4',k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37746,c_37531])).

tff(c_37752,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37527,c_37748])).

tff(c_37753,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_37738])).

tff(c_27371,plain,(
    ! [B_1417] :
      ( k1_relset_1(B_1417,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_1417) ) ),
    inference(resolution,[status(thm)],[c_27339,c_18])).

tff(c_37594,plain,(
    ! [B_2061] :
      ( k1_relset_1(B_2061,k1_xboole_0,'#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_2061) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37525,c_27371])).

tff(c_37610,plain,(
    k1_relset_1(k1_relat_1('#skF_4'),k1_xboole_0,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_37594])).

tff(c_37758,plain,(
    k1_relset_1(k1_relat_1('#skF_4'),'#skF_4','#skF_4') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37753,c_37610])).

tff(c_37526,plain,(
    u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) != k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_34929])).

tff(c_37530,plain,(
    k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),k1_xboole_0,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37525,c_34843])).

tff(c_37942,plain,(
    k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),'#skF_4','#skF_4') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37753,c_37530])).

tff(c_37764,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37753,c_37525])).

tff(c_34735,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0
    | k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') = u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(resolution,[status(thm)],[c_60,c_34726])).

tff(c_34743,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0
    | k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') = u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_34735])).

tff(c_37845,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = '#skF_4'
    | k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') = u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34747,c_34747,c_37753,c_34743])).

tff(c_37846,plain,(
    k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') = u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_37845])).

tff(c_38681,plain,(
    u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37942,c_37764,c_37846])).

tff(c_38682,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37526,c_38681])).

tff(c_38683,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_37845])).

tff(c_36,plain,(
    ! [C_23,A_21,B_22] :
      ( v1_funct_2(C_23,A_21,B_22)
      | k1_relset_1(A_21,B_22,C_23) != A_21
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22)))
      | ~ v1_funct_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_27342,plain,(
    ! [B_1417] :
      ( v1_funct_2('#skF_4',B_1417,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | k1_relset_1(B_1417,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') != B_1417
      | ~ v1_funct_1('#skF_4')
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_1417) ) ),
    inference(resolution,[status(thm)],[c_27339,c_36])).

tff(c_27367,plain,(
    ! [B_1417] :
      ( v1_funct_2('#skF_4',B_1417,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | k1_relset_1(B_1417,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') != B_1417
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_1417) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_27342])).

tff(c_39633,plain,(
    ! [B_2163] :
      ( v1_funct_2('#skF_4',B_2163,'#skF_4')
      | k1_relset_1(B_2163,'#skF_4','#skF_4') != B_2163
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_2163) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38683,c_38683,c_27367])).

tff(c_39644,plain,
    ( v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_4')
    | k1_relset_1(k1_relat_1('#skF_4'),'#skF_4','#skF_4') != k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_39633])).

tff(c_39653,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37758,c_39644])).

tff(c_37532,plain,(
    ! [B_1408] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_1408,k1_xboole_0)))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_1408) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37525,c_27256])).

tff(c_37757,plain,(
    ! [B_1408] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_1408,'#skF_4')))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_1408) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37753,c_37532])).

tff(c_56,plain,(
    ! [D_57,A_43,B_51] :
      ( v5_pre_topc(D_57,A_43,g1_pre_topc(u1_struct_0(B_51),u1_pre_topc(B_51)))
      | ~ v5_pre_topc(D_57,A_43,B_51)
      | ~ m1_subset_1(D_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_43),u1_struct_0(g1_pre_topc(u1_struct_0(B_51),u1_pre_topc(B_51))))))
      | ~ v1_funct_2(D_57,u1_struct_0(A_43),u1_struct_0(g1_pre_topc(u1_struct_0(B_51),u1_pre_topc(B_51))))
      | ~ m1_subset_1(D_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_43),u1_struct_0(B_51))))
      | ~ v1_funct_2(D_57,u1_struct_0(A_43),u1_struct_0(B_51))
      | ~ v1_funct_1(D_57)
      | ~ l1_pre_topc(B_51)
      | ~ v2_pre_topc(B_51)
      | ~ l1_pre_topc(A_43)
      | ~ v2_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_38704,plain,(
    ! [D_57,A_43] :
      ( v5_pre_topc(D_57,A_43,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc(D_57,A_43,'#skF_2')
      | ~ m1_subset_1(D_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_43),'#skF_4')))
      | ~ v1_funct_2(D_57,u1_struct_0(A_43),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1(D_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_43),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_57,u1_struct_0(A_43),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_57)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_43)
      | ~ v2_pre_topc(A_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38683,c_56])).

tff(c_40034,plain,(
    ! [D_2194,A_2195] :
      ( v5_pre_topc(D_2194,A_2195,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc(D_2194,A_2195,'#skF_2')
      | ~ m1_subset_1(D_2194,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2195),'#skF_4')))
      | ~ v1_funct_2(D_2194,u1_struct_0(A_2195),'#skF_4')
      | ~ m1_subset_1(D_2194,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2195),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_2194,u1_struct_0(A_2195),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_2194)
      | ~ l1_pre_topc(A_2195)
      | ~ v2_pre_topc(A_2195) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_38683,c_38704])).

tff(c_40040,plain,(
    ! [D_2194] :
      ( v5_pre_topc(D_2194,'#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc(D_2194,'#skF_1','#skF_2')
      | ~ m1_subset_1(D_2194,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),'#skF_4')))
      | ~ v1_funct_2(D_2194,u1_struct_0('#skF_1'),'#skF_4')
      | ~ m1_subset_1(D_2194,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_2194,u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_2194)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34747,c_40034])).

tff(c_40085,plain,(
    ! [D_2198] :
      ( v5_pre_topc(D_2198,'#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc(D_2198,'#skF_1','#skF_2')
      | ~ m1_subset_1(D_2198,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_4')))
      | ~ v1_funct_2(D_2198,k1_relat_1('#skF_4'),'#skF_4')
      | ~ m1_subset_1(D_2198,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_2198,k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_2198) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_34747,c_34747,c_34747,c_40040])).

tff(c_40088,plain,
    ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_4')))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_4')
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34753,c_40085])).

tff(c_40095,plain,
    ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_34755,c_39653,c_27217,c_40088])).

tff(c_40099,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_40095])).

tff(c_40102,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_37757,c_40099])).

tff(c_40106,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_40102])).

tff(c_40108,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_40095])).

tff(c_37761,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37753,c_37531])).

tff(c_37755,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),'#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37753,c_37528])).

tff(c_40107,plain,(
    v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_40095])).

tff(c_37549,plain,
    ( v1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_37525,c_149])).

tff(c_39704,plain,
    ( v1_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37753,c_37549])).

tff(c_39705,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_39704])).

tff(c_39710,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_120,c_39705])).

tff(c_39714,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_39710])).

tff(c_39716,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_39704])).

tff(c_34857,plain,(
    ! [D_1923,A_1924,B_1925] :
      ( v5_pre_topc(D_1923,A_1924,B_1925)
      | ~ v5_pre_topc(D_1923,g1_pre_topc(u1_struct_0(A_1924),u1_pre_topc(A_1924)),B_1925)
      | ~ m1_subset_1(D_1923,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1924),u1_pre_topc(A_1924))),u1_struct_0(B_1925))))
      | ~ v1_funct_2(D_1923,u1_struct_0(g1_pre_topc(u1_struct_0(A_1924),u1_pre_topc(A_1924))),u1_struct_0(B_1925))
      | ~ m1_subset_1(D_1923,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1924),u1_struct_0(B_1925))))
      | ~ v1_funct_2(D_1923,u1_struct_0(A_1924),u1_struct_0(B_1925))
      | ~ v1_funct_1(D_1923)
      | ~ l1_pre_topc(B_1925)
      | ~ v2_pre_topc(B_1925)
      | ~ l1_pre_topc(A_1924)
      | ~ v2_pre_topc(A_1924) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_34867,plain,(
    ! [A_1924] :
      ( v5_pre_topc('#skF_4',A_1924,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_1924),u1_pre_topc(A_1924)),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_1924),u1_pre_topc(A_1924))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1924),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1924),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_1924)
      | ~ v2_pre_topc(A_1924)
      | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0(A_1924),u1_pre_topc(A_1924)))) ) ),
    inference(resolution,[status(thm)],[c_27256,c_34857])).

tff(c_34878,plain,(
    ! [A_1924] :
      ( v5_pre_topc('#skF_4',A_1924,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_1924),u1_pre_topc(A_1924)),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_1924),u1_pre_topc(A_1924))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1924),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1924),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_1924)
      | ~ v2_pre_topc(A_1924)
      | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0(A_1924),u1_pre_topc(A_1924)))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_34867])).

tff(c_39787,plain,(
    ! [A_1924] :
      ( v5_pre_topc('#skF_4',A_1924,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_1924),u1_pre_topc(A_1924)),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_1924),u1_pre_topc(A_1924))),'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1924),'#skF_4')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1924),'#skF_4')
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_1924)
      | ~ v2_pre_topc(A_1924)
      | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0(A_1924),u1_pre_topc(A_1924)))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39716,c_38683,c_38683,c_38683,c_34878])).

tff(c_39788,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_39787])).

tff(c_39791,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_39788])).

tff(c_39795,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_39791])).

tff(c_39797,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_39787])).

tff(c_37563,plain,(
    ! [D_2058,A_2059,B_2060] :
      ( v5_pre_topc(D_2058,g1_pre_topc(u1_struct_0(A_2059),u1_pre_topc(A_2059)),B_2060)
      | ~ v5_pre_topc(D_2058,A_2059,B_2060)
      | ~ m1_subset_1(D_2058,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2059),u1_pre_topc(A_2059))),u1_struct_0(B_2060))))
      | ~ v1_funct_2(D_2058,u1_struct_0(g1_pre_topc(u1_struct_0(A_2059),u1_pre_topc(A_2059))),u1_struct_0(B_2060))
      | ~ m1_subset_1(D_2058,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2059),u1_struct_0(B_2060))))
      | ~ v1_funct_2(D_2058,u1_struct_0(A_2059),u1_struct_0(B_2060))
      | ~ v1_funct_1(D_2058)
      | ~ l1_pre_topc(B_2060)
      | ~ v2_pre_topc(B_2060)
      | ~ l1_pre_topc(A_2059)
      | ~ v2_pre_topc(A_2059) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_37575,plain,(
    ! [D_2058,B_2060] :
      ( v5_pre_topc(D_2058,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_2060)
      | ~ v5_pre_topc(D_2058,'#skF_1',B_2060)
      | ~ m1_subset_1(D_2058,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(B_2060))))
      | ~ v1_funct_2(D_2058,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_2060))
      | ~ m1_subset_1(D_2058,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_2060))))
      | ~ v1_funct_2(D_2058,u1_struct_0('#skF_1'),u1_struct_0(B_2060))
      | ~ v1_funct_1(D_2058)
      | ~ l1_pre_topc(B_2060)
      | ~ v2_pre_topc(B_2060)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34747,c_37563])).

tff(c_40295,plain,(
    ! [D_2209,B_2210] :
      ( v5_pre_topc(D_2209,g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),B_2210)
      | ~ v5_pre_topc(D_2209,'#skF_1',B_2210)
      | ~ m1_subset_1(D_2209,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(B_2210))))
      | ~ v1_funct_2(D_2209,u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(B_2210))
      | ~ m1_subset_1(D_2209,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_2210))))
      | ~ v1_funct_2(D_2209,k1_relat_1('#skF_4'),u1_struct_0(B_2210))
      | ~ v1_funct_1(D_2209)
      | ~ l1_pre_topc(B_2210)
      | ~ v2_pre_topc(B_2210) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_34747,c_34747,c_34747,c_34747,c_37575])).

tff(c_40298,plain,(
    ! [D_2209] :
      ( v5_pre_topc(D_2209,g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc(D_2209,'#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ m1_subset_1(D_2209,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),'#skF_4')))
      | ~ v1_funct_2(D_2209,u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1(D_2209,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))))
      | ~ v1_funct_2(D_2209,k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ v1_funct_1(D_2209)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38683,c_40295])).

tff(c_40469,plain,(
    ! [D_2230] :
      ( v5_pre_topc(D_2230,g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc(D_2230,'#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ m1_subset_1(D_2230,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),'#skF_4')))
      | ~ v1_funct_2(D_2230,u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),'#skF_4')
      | ~ m1_subset_1(D_2230,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_4')))
      | ~ v1_funct_2(D_2230,k1_relat_1('#skF_4'),'#skF_4')
      | ~ v1_funct_1(D_2230) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39797,c_39716,c_38683,c_38683,c_38683,c_40298])).

tff(c_40479,plain,
    ( ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),'#skF_4')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),'#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_4')))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_4')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40469,c_34749])).

tff(c_40487,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_39653,c_40108,c_37761,c_37755,c_40107,c_40479])).

tff(c_40488,plain,(
    k1_relset_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_34943])).

tff(c_40517,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_40488,c_27371])).

tff(c_40524,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34691,c_40517])).

tff(c_40526,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34856,c_40524])).

tff(c_40527,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_34848])).

tff(c_34708,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_34691,c_2])).

tff(c_34792,plain,(
    ~ r1_tarski(k1_xboole_0,k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_34708])).

tff(c_40532,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40527,c_34792])).

tff(c_40551,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_40532])).

tff(c_40552,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_34708])).

tff(c_40929,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40552,c_34749])).

tff(c_40566,plain,(
    u1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40552,c_34747])).

tff(c_40554,plain,(
    k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34747,c_27228])).

tff(c_40559,plain,(
    k1_relset_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40552,c_40552,c_40554])).

tff(c_43961,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40566,c_40559,c_40566,c_34743])).

tff(c_43962,plain,(
    u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1'))) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_43961])).

tff(c_40629,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40552,c_34752])).

tff(c_16,plain,(
    ! [C_10,A_8,B_9] :
      ( v4_relat_1(C_10,A_8)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_40662,plain,(
    v4_relat_1('#skF_4',u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1')))) ),
    inference(resolution,[status(thm)],[c_40629,c_16])).

tff(c_40581,plain,(
    ! [A_78] :
      ( k1_relat_1('#skF_4') = A_78
      | ~ r1_tarski(A_78,k1_xboole_0)
      | ~ v4_relat_1('#skF_4',A_78)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40552,c_115])).

tff(c_40777,plain,(
    ! [A_2242] :
      ( k1_xboole_0 = A_2242
      | ~ r1_tarski(A_2242,k1_xboole_0)
      | ~ v4_relat_1('#skF_4',A_2242) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_40552,c_40581])).

tff(c_40791,plain,
    ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1'))) = k1_xboole_0
    | ~ r1_tarski(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1'))),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_40662,c_40777])).

tff(c_40930,plain,(
    ~ r1_tarski(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1'))),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_40791])).

tff(c_43964,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43962,c_40930])).

tff(c_43972,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_43964])).

tff(c_43974,plain,(
    u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1'))) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_43961])).

tff(c_43973,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_43961])).

tff(c_40564,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40552,c_34754])).

tff(c_43980,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1'))),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43973,c_40564])).

tff(c_43981,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1'))),k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43973,c_40629])).

tff(c_44144,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1'))),k1_xboole_0)
    | u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1'))) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_43981,c_24])).

tff(c_44171,plain,
    ( k1_xboole_0 = '#skF_4'
    | u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_43980,c_44144])).

tff(c_44172,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_43974,c_44171])).

tff(c_44190,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44172,c_43973])).

tff(c_40570,plain,(
    ! [B_1408] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_1408,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))))
      | ~ r1_tarski(k1_xboole_0,B_1408) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40552,c_27256])).

tff(c_43978,plain,(
    ! [B_1408] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_1408,k1_xboole_0)))
      | ~ r1_tarski(k1_xboole_0,B_1408) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43973,c_40570])).

tff(c_44183,plain,(
    ! [B_1408] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_1408,'#skF_4')))
      | ~ r1_tarski('#skF_4',B_1408) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44172,c_44172,c_43978])).

tff(c_44197,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44172,c_40929])).

tff(c_44203,plain,(
    v4_relat_1('#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44172,c_40662])).

tff(c_40590,plain,(
    ! [A_3] :
      ( r1_tarski(k1_xboole_0,A_3)
      | ~ v4_relat_1('#skF_4',A_3)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40552,c_10])).

tff(c_40600,plain,(
    ! [A_3] :
      ( r1_tarski(k1_xboole_0,A_3)
      | ~ v4_relat_1('#skF_4',A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_40590])).

tff(c_44205,plain,(
    ! [A_3] :
      ( r1_tarski('#skF_4',A_3)
      | ~ v4_relat_1('#skF_4',A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44172,c_40600])).

tff(c_44442,plain,(
    r1_tarski('#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')))) ),
    inference(resolution,[status(thm)],[c_44203,c_44205])).

tff(c_44214,plain,(
    u1_struct_0('#skF_1') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44172,c_40566])).

tff(c_41026,plain,(
    ! [B_1417] :
      ( k1_relset_1(B_1417,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,B_1417) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40552,c_40552,c_27371])).

tff(c_27370,plain,
    ( v1_funct_2('#skF_4',k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
    | k1_relset_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') != k1_xboole_0
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_27339,c_26])).

tff(c_41110,plain,
    ( v1_funct_2('#skF_4',k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
    | k1_relset_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_40552,c_27370])).

tff(c_41111,plain,(
    k1_relset_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_41110])).

tff(c_41114,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_41026,c_41111])).

tff(c_41118,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_41114])).

tff(c_41119,plain,(
    v1_funct_2('#skF_4',k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_41110])).

tff(c_43976,plain,(
    v1_funct_2('#skF_4',k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43973,c_41119])).

tff(c_44188,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44172,c_44172,c_43976])).

tff(c_44186,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44172,c_44172,c_43980])).

tff(c_40565,plain,(
    v1_funct_2('#skF_4',k1_xboole_0,u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40552,c_34755])).

tff(c_44209,plain,(
    v1_funct_2('#skF_4','#skF_4',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44172,c_40565])).

tff(c_40714,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40552,c_34753])).

tff(c_44204,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4',u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44172,c_40714])).

tff(c_40953,plain,(
    ! [B_2252] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_2252,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))))
      | ~ r1_tarski(k1_xboole_0,B_2252) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40552,c_27256])).

tff(c_41007,plain,(
    ! [B_2252] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0
      | k1_relset_1(B_2252,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') = B_2252
      | ~ v1_funct_2('#skF_4',B_2252,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ r1_tarski(k1_xboole_0,B_2252) ) ),
    inference(resolution,[status(thm)],[c_40953,c_32])).

tff(c_44336,plain,(
    ! [B_2252] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = '#skF_4'
      | k1_relset_1(B_2252,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') = B_2252
      | ~ v1_funct_2('#skF_4',B_2252,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ r1_tarski('#skF_4',B_2252) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44172,c_44172,c_41007])).

tff(c_44337,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_44336])).

tff(c_40957,plain,(
    ! [A_43] :
      ( v5_pre_topc('#skF_4',A_43,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc('#skF_4',A_43,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_43),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_43),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_43),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_43)
      | ~ v2_pre_topc(A_43)
      | ~ r1_tarski(k1_xboole_0,u1_struct_0(A_43)) ) ),
    inference(resolution,[status(thm)],[c_40953,c_56])).

tff(c_40999,plain,(
    ! [A_43] :
      ( v5_pre_topc('#skF_4',A_43,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc('#skF_4',A_43,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_43),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_43),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_43),u1_struct_0('#skF_2'))
      | ~ l1_pre_topc(A_43)
      | ~ v2_pre_topc(A_43)
      | ~ r1_tarski(k1_xboole_0,u1_struct_0(A_43)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_64,c_40957])).

tff(c_44895,plain,(
    ! [A_2356] :
      ( v5_pre_topc('#skF_4',A_2356,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc('#skF_4',A_2356,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_2356),'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2356),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_2356),u1_struct_0('#skF_2'))
      | ~ l1_pre_topc(A_2356)
      | ~ v2_pre_topc(A_2356)
      | ~ r1_tarski('#skF_4',u1_struct_0(A_2356)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44172,c_44337,c_40999])).

tff(c_44904,plain,
    ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4',u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ r1_tarski('#skF_4',u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_44214,c_44895])).

tff(c_44909,plain,(
    v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_44214,c_78,c_76,c_44209,c_44214,c_44204,c_44188,c_44214,c_27217,c_44904])).

tff(c_44025,plain,
    ( v1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_43973,c_149])).

tff(c_44737,plain,
    ( v1_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44172,c_44025])).

tff(c_44738,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_44737])).

tff(c_44741,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_120,c_44738])).

tff(c_44745,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_44741])).

tff(c_44747,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_44737])).

tff(c_44022,plain,
    ( v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_43973,c_46])).

tff(c_44861,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44747,c_44172,c_44022])).

tff(c_44862,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_44861])).

tff(c_44865,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_44862])).

tff(c_44869,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_44865])).

tff(c_44871,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_44861])).

tff(c_40961,plain,(
    ! [A_28] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_28),u1_pre_topc(A_28)),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc('#skF_4',A_28,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_28),u1_pre_topc(A_28))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_28),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_28),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_28)
      | ~ v2_pre_topc(A_28)
      | ~ r1_tarski(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(A_28),u1_pre_topc(A_28)))) ) ),
    inference(resolution,[status(thm)],[c_40953,c_52])).

tff(c_41002,plain,(
    ! [A_28] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_28),u1_pre_topc(A_28)),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc('#skF_4',A_28,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_28),u1_pre_topc(A_28))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_28),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_28),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_28)
      | ~ v2_pre_topc(A_28)
      | ~ r1_tarski(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(A_28),u1_pre_topc(A_28)))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_40961])).

tff(c_45007,plain,(
    ! [A_2366] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_2366),u1_pre_topc(A_2366)),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc('#skF_4',A_2366,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_2366),u1_pre_topc(A_2366))),'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2366),'#skF_4')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_2366),'#skF_4')
      | ~ l1_pre_topc(A_2366)
      | ~ v2_pre_topc(A_2366)
      | ~ r1_tarski('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_2366),u1_pre_topc(A_2366)))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44172,c_44871,c_44747,c_44337,c_44337,c_44337,c_41002])).

tff(c_45019,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),'#skF_4')))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ r1_tarski('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_44214,c_45007])).

tff(c_45027,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44442,c_44214,c_78,c_76,c_44188,c_44214,c_44214,c_44186,c_44214,c_44909,c_45019])).

tff(c_45028,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_44197,c_45027])).

tff(c_45031,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_44183,c_45028])).

tff(c_45035,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_45031])).

tff(c_45037,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_44336])).

tff(c_45175,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44190,c_45037])).

tff(c_45176,plain,(
    u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1'))) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_40791])).

tff(c_40563,plain,(
    v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40552,c_34774])).

tff(c_40562,plain,(
    l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40552,c_34778])).

tff(c_45178,plain,(
    v1_funct_2('#skF_4',k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45176,c_40564])).

tff(c_45390,plain,(
    ! [D_2372,A_2373,B_2374] :
      ( v5_pre_topc(D_2372,A_2373,g1_pre_topc(u1_struct_0(B_2374),u1_pre_topc(B_2374)))
      | ~ v5_pre_topc(D_2372,A_2373,B_2374)
      | ~ m1_subset_1(D_2372,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2373),u1_struct_0(g1_pre_topc(u1_struct_0(B_2374),u1_pre_topc(B_2374))))))
      | ~ v1_funct_2(D_2372,u1_struct_0(A_2373),u1_struct_0(g1_pre_topc(u1_struct_0(B_2374),u1_pre_topc(B_2374))))
      | ~ m1_subset_1(D_2372,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2373),u1_struct_0(B_2374))))
      | ~ v1_funct_2(D_2372,u1_struct_0(A_2373),u1_struct_0(B_2374))
      | ~ v1_funct_1(D_2372)
      | ~ l1_pre_topc(B_2374)
      | ~ v2_pre_topc(B_2374)
      | ~ l1_pre_topc(A_2373)
      | ~ v2_pre_topc(A_2373) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_45394,plain,(
    ! [A_2373] :
      ( v5_pre_topc('#skF_4',A_2373,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc('#skF_4',A_2373,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_2373),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2373),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_2373),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_2373)
      | ~ v2_pre_topc(A_2373)
      | ~ r1_tarski(k1_xboole_0,u1_struct_0(A_2373)) ) ),
    inference(resolution,[status(thm)],[c_40570,c_45390])).

tff(c_53663,plain,(
    ! [A_2689] :
      ( v5_pre_topc('#skF_4',A_2689,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc('#skF_4',A_2689,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_2689),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2689),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_2689),u1_struct_0('#skF_2'))
      | ~ l1_pre_topc(A_2689)
      | ~ v2_pre_topc(A_2689)
      | ~ r1_tarski(k1_xboole_0,u1_struct_0(A_2689)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_64,c_45394])).

tff(c_53669,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1')),'#skF_2')
    | ~ v1_funct_2('#skF_4',k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2'))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1')))
    | ~ v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1')))
    | ~ r1_tarski(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_45176,c_53663])).

tff(c_53675,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_45176,c_40563,c_40562,c_40565,c_45176,c_40714,c_45176,c_45178,c_53669])).

tff(c_53676,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_40929,c_53675])).

tff(c_40861,plain,(
    ! [B_2248] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_2248,u1_struct_0('#skF_2'))))
      | ~ r1_tarski(k1_xboole_0,B_2248) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40552,c_27257])).

tff(c_40865,plain,(
    ! [A_28] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_28),u1_pre_topc(A_28)),'#skF_2')
      | ~ v5_pre_topc('#skF_4',A_28,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_28),u1_pre_topc(A_28))),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_28),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_28),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_28)
      | ~ v2_pre_topc(A_28)
      | ~ r1_tarski(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(A_28),u1_pre_topc(A_28)))) ) ),
    inference(resolution,[status(thm)],[c_40861,c_52])).

tff(c_53801,plain,(
    ! [A_2698] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_2698),u1_pre_topc(A_2698)),'#skF_2')
      | ~ v5_pre_topc('#skF_4',A_2698,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_2698),u1_pre_topc(A_2698))),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2698),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_2698),u1_struct_0('#skF_2'))
      | ~ l1_pre_topc(A_2698)
      | ~ v2_pre_topc(A_2698)
      | ~ r1_tarski(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(A_2698),u1_pre_topc(A_2698)))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_64,c_40865])).

tff(c_53810,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ r1_tarski(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_40566,c_53801])).

tff(c_53815,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_45176,c_40566,c_78,c_76,c_40565,c_40566,c_40714,c_40566,c_40565,c_45176,c_27217,c_40566,c_53810])).

tff(c_53817,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53676,c_53815])).

tff(c_53818,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_34746])).

tff(c_53852,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53818,c_87])).

tff(c_53850,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53818,c_91])).

tff(c_53915,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),k1_xboole_0)
    | u1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_53850,c_24])).

tff(c_53941,plain,
    ( k1_xboole_0 = '#skF_4'
    | u1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_53852,c_53915])).

tff(c_53949,plain,(
    u1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_53941])).

tff(c_53819,plain,(
    u1_struct_0('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_34746])).

tff(c_53998,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_53949,c_53819])).

tff(c_53996,plain,(
    v1_funct_2('#skF_4',k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53949,c_53852])).

tff(c_53839,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53818,c_34703])).

tff(c_53995,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53949,c_53850])).

tff(c_54070,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_4',k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_53995,c_30])).

tff(c_54102,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_53996,c_53839,c_54070])).

tff(c_54104,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53998,c_54102])).

tff(c_54105,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_53941])).

tff(c_53846,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53818,c_27218])).

tff(c_56387,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54105,c_53846])).

tff(c_53856,plain,
    ( v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_53818,c_46])).

tff(c_53869,plain,(
    v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_53856])).

tff(c_54110,plain,(
    v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54105,c_53869])).

tff(c_53862,plain,
    ( l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_53818,c_120])).

tff(c_53873,plain,(
    l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_53862])).

tff(c_54112,plain,(
    l1_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54105,c_53873])).

tff(c_54113,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54105,c_53852])).

tff(c_53851,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53818,c_62])).

tff(c_54114,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54105,c_53851])).

tff(c_54107,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),'#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54105,c_53850])).

tff(c_53844,plain,(
    ! [B_1408] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_1408,k1_xboole_0)))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_1408) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53818,c_27257])).

tff(c_54350,plain,(
    ! [B_1408] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_1408,'#skF_4')))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_1408) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54105,c_53844])).

tff(c_54400,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54105,c_53846])).

tff(c_54116,plain,(
    u1_struct_0('#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54105,c_53818])).

tff(c_54229,plain,(
    k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))),'#skF_4') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54116,c_27228])).

tff(c_54569,plain,
    ( u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) = '#skF_4'
    | u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54229,c_54116,c_54105,c_54116,c_34743])).

tff(c_54570,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_54569])).

tff(c_54620,plain,
    ( v1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_54570,c_149])).

tff(c_54745,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_54620])).

tff(c_54751,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_120,c_54745])).

tff(c_54755,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_54751])).

tff(c_54757,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_54620])).

tff(c_54617,plain,
    ( v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_54570,c_46])).

tff(c_54829,plain,
    ( v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54757,c_54617])).

tff(c_54830,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_54829])).

tff(c_54833,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_54830])).

tff(c_54837,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_54833])).

tff(c_54839,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_54829])).

tff(c_54403,plain,(
    ! [A_2720] :
      ( v1_funct_2('#skF_4',A_2720,'#skF_4')
      | A_2720 = '#skF_4'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_2720,'#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54105,c_54105,c_54105,c_54105,c_54105,c_22])).

tff(c_54414,plain,(
    ! [B_2721] :
      ( v1_funct_2('#skF_4',B_2721,'#skF_4')
      | B_2721 = '#skF_4'
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_2721) ) ),
    inference(resolution,[status(thm)],[c_54350,c_54403])).

tff(c_54433,plain,
    ( v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_4')
    | k1_relat_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6,c_54414])).

tff(c_54434,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_54433])).

tff(c_54120,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54105,c_34691])).

tff(c_54211,plain,
    ( k1_relat_1('#skF_4') = '#skF_4'
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_54120,c_2])).

tff(c_54304,plain,(
    ~ r1_tarski('#skF_4',k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_54211])).

tff(c_54440,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54434,c_54304])).

tff(c_54451,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_54440])).

tff(c_54452,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_54433])).

tff(c_54571,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54570,c_54114])).

tff(c_53887,plain,(
    ! [D_2702,A_2703,B_2704] :
      ( v5_pre_topc(D_2702,g1_pre_topc(u1_struct_0(A_2703),u1_pre_topc(A_2703)),B_2704)
      | ~ v5_pre_topc(D_2702,A_2703,B_2704)
      | ~ m1_subset_1(D_2702,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2703),u1_pre_topc(A_2703))),u1_struct_0(B_2704))))
      | ~ v1_funct_2(D_2702,u1_struct_0(g1_pre_topc(u1_struct_0(A_2703),u1_pre_topc(A_2703))),u1_struct_0(B_2704))
      | ~ m1_subset_1(D_2702,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2703),u1_struct_0(B_2704))))
      | ~ v1_funct_2(D_2702,u1_struct_0(A_2703),u1_struct_0(B_2704))
      | ~ v1_funct_1(D_2702)
      | ~ l1_pre_topc(B_2704)
      | ~ v2_pre_topc(B_2704)
      | ~ l1_pre_topc(A_2703)
      | ~ v2_pre_topc(A_2703) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_53893,plain,(
    ! [D_2702,A_2703] :
      ( v5_pre_topc(D_2702,g1_pre_topc(u1_struct_0(A_2703),u1_pre_topc(A_2703)),'#skF_2')
      | ~ v5_pre_topc(D_2702,A_2703,'#skF_2')
      | ~ m1_subset_1(D_2702,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2703),u1_pre_topc(A_2703))),k1_xboole_0)))
      | ~ v1_funct_2(D_2702,u1_struct_0(g1_pre_topc(u1_struct_0(A_2703),u1_pre_topc(A_2703))),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(D_2702,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2703),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_2702,u1_struct_0(A_2703),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_2702)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_2703)
      | ~ v2_pre_topc(A_2703) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53818,c_53887])).

tff(c_53897,plain,(
    ! [D_2702,A_2703] :
      ( v5_pre_topc(D_2702,g1_pre_topc(u1_struct_0(A_2703),u1_pre_topc(A_2703)),'#skF_2')
      | ~ v5_pre_topc(D_2702,A_2703,'#skF_2')
      | ~ m1_subset_1(D_2702,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2703),u1_pre_topc(A_2703))),k1_xboole_0)))
      | ~ v1_funct_2(D_2702,u1_struct_0(g1_pre_topc(u1_struct_0(A_2703),u1_pre_topc(A_2703))),k1_xboole_0)
      | ~ m1_subset_1(D_2702,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2703),k1_xboole_0)))
      | ~ v1_funct_2(D_2702,u1_struct_0(A_2703),k1_xboole_0)
      | ~ v1_funct_1(D_2702)
      | ~ l1_pre_topc(A_2703)
      | ~ v2_pre_topc(A_2703) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_53818,c_53818,c_53818,c_53893])).

tff(c_55628,plain,(
    ! [D_2804,A_2805] :
      ( v5_pre_topc(D_2804,g1_pre_topc(u1_struct_0(A_2805),u1_pre_topc(A_2805)),'#skF_2')
      | ~ v5_pre_topc(D_2804,A_2805,'#skF_2')
      | ~ m1_subset_1(D_2804,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2805),u1_pre_topc(A_2805))),'#skF_4')))
      | ~ v1_funct_2(D_2804,u1_struct_0(g1_pre_topc(u1_struct_0(A_2805),u1_pre_topc(A_2805))),'#skF_4')
      | ~ m1_subset_1(D_2804,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2805),'#skF_4')))
      | ~ v1_funct_2(D_2804,u1_struct_0(A_2805),'#skF_4')
      | ~ v1_funct_1(D_2804)
      | ~ l1_pre_topc(A_2805)
      | ~ v2_pre_topc(A_2805) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54105,c_54105,c_54105,c_54105,c_53897])).

tff(c_55638,plain,(
    ! [A_2805] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_2805),u1_pre_topc(A_2805)),'#skF_2')
      | ~ v5_pre_topc('#skF_4',A_2805,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_2805),u1_pre_topc(A_2805))),'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2805),'#skF_4')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_2805),'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(A_2805)
      | ~ v2_pre_topc(A_2805)
      | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0(A_2805),u1_pre_topc(A_2805)))) ) ),
    inference(resolution,[status(thm)],[c_54350,c_55628])).

tff(c_55651,plain,(
    ! [A_2806] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_2806),u1_pre_topc(A_2806)),'#skF_2')
      | ~ v5_pre_topc('#skF_4',A_2806,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_2806),u1_pre_topc(A_2806))),'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2806),'#skF_4')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_2806),'#skF_4')
      | ~ l1_pre_topc(A_2806)
      | ~ v2_pre_topc(A_2806)
      | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0(A_2806),u1_pre_topc(A_2806)))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_55638])).

tff(c_55657,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),'#skF_4')))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_54570,c_55651])).

tff(c_55667,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_78,c_76,c_54113,c_54107,c_54452,c_54570,c_27217,c_55657])).

tff(c_53841,plain,(
    ! [B_1408] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_1408,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2'))))))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_1408) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53818,c_27256])).

tff(c_54454,plain,(
    ! [B_1408] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_1408,u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_1408) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54105,c_53841])).

tff(c_54305,plain,(
    ! [D_2714,A_2715,B_2716] :
      ( v5_pre_topc(D_2714,A_2715,g1_pre_topc(u1_struct_0(B_2716),u1_pre_topc(B_2716)))
      | ~ v5_pre_topc(D_2714,A_2715,B_2716)
      | ~ m1_subset_1(D_2714,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2715),u1_struct_0(g1_pre_topc(u1_struct_0(B_2716),u1_pre_topc(B_2716))))))
      | ~ v1_funct_2(D_2714,u1_struct_0(A_2715),u1_struct_0(g1_pre_topc(u1_struct_0(B_2716),u1_pre_topc(B_2716))))
      | ~ m1_subset_1(D_2714,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2715),u1_struct_0(B_2716))))
      | ~ v1_funct_2(D_2714,u1_struct_0(A_2715),u1_struct_0(B_2716))
      | ~ v1_funct_1(D_2714)
      | ~ l1_pre_topc(B_2716)
      | ~ v2_pre_topc(B_2716)
      | ~ l1_pre_topc(A_2715)
      | ~ v2_pre_topc(A_2715) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_54311,plain,(
    ! [D_2714,A_2715] :
      ( v5_pre_topc(D_2714,A_2715,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc(D_2714,A_2715,'#skF_2')
      | ~ m1_subset_1(D_2714,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2715),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))))
      | ~ v1_funct_2(D_2714,u1_struct_0(A_2715),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1(D_2714,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2715),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_2714,u1_struct_0(A_2715),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_2714)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_2715)
      | ~ v2_pre_topc(A_2715) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54116,c_54305])).

tff(c_55839,plain,(
    ! [D_2820,A_2821] :
      ( v5_pre_topc(D_2820,A_2821,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc(D_2820,A_2821,'#skF_2')
      | ~ m1_subset_1(D_2820,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2821),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))))
      | ~ v1_funct_2(D_2820,u1_struct_0(A_2821),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1(D_2820,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2821),'#skF_4')))
      | ~ v1_funct_2(D_2820,u1_struct_0(A_2821),'#skF_4')
      | ~ v1_funct_1(D_2820)
      | ~ l1_pre_topc(A_2821)
      | ~ v2_pre_topc(A_2821) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_54116,c_54116,c_54116,c_54116,c_54311])).

tff(c_55846,plain,(
    ! [A_2821] :
      ( v5_pre_topc('#skF_4',A_2821,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc('#skF_4',A_2821,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_2821),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2821),'#skF_4')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_2821),'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(A_2821)
      | ~ v2_pre_topc(A_2821)
      | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(A_2821)) ) ),
    inference(resolution,[status(thm)],[c_54454,c_55839])).

tff(c_55875,plain,(
    ! [A_2824] :
      ( v5_pre_topc('#skF_4',A_2824,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc('#skF_4',A_2824,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_2824),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2824),'#skF_4')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_2824),'#skF_4')
      | ~ l1_pre_topc(A_2824)
      | ~ v2_pre_topc(A_2824)
      | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(A_2824)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_55846])).

tff(c_55881,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_54570,c_55875])).

tff(c_55887,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_54570,c_54839,c_54757,c_54452,c_54570,c_54570,c_54571,c_55667,c_55881])).

tff(c_55888,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54400,c_55887])).

tff(c_55893,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_54350,c_55888])).

tff(c_55897,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_55893])).

tff(c_55898,plain,(
    u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_54569])).

tff(c_55902,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55898,c_54114])).

tff(c_53848,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53818,c_60])).

tff(c_54129,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54105,c_53848])).

tff(c_55905,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55898,c_54129])).

tff(c_56143,plain,(
    ! [D_2843,A_2844] :
      ( v5_pre_topc(D_2843,g1_pre_topc(u1_struct_0(A_2844),u1_pre_topc(A_2844)),'#skF_2')
      | ~ v5_pre_topc(D_2843,A_2844,'#skF_2')
      | ~ m1_subset_1(D_2843,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2844),u1_pre_topc(A_2844))),'#skF_4')))
      | ~ v1_funct_2(D_2843,u1_struct_0(g1_pre_topc(u1_struct_0(A_2844),u1_pre_topc(A_2844))),'#skF_4')
      | ~ m1_subset_1(D_2843,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2844),'#skF_4')))
      | ~ v1_funct_2(D_2843,u1_struct_0(A_2844),'#skF_4')
      | ~ v1_funct_1(D_2843)
      | ~ l1_pre_topc(A_2844)
      | ~ v2_pre_topc(A_2844) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54105,c_54105,c_54105,c_54105,c_53897])).

tff(c_56146,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),'#skF_4')))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_55905,c_56143])).

tff(c_56159,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_64,c_54113,c_54107,c_55902,c_27217,c_56146])).

tff(c_54315,plain,(
    ! [D_2714,A_2715] :
      ( v5_pre_topc(D_2714,A_2715,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc(D_2714,A_2715,'#skF_2')
      | ~ m1_subset_1(D_2714,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2715),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))))
      | ~ v1_funct_2(D_2714,u1_struct_0(A_2715),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1(D_2714,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2715),'#skF_4')))
      | ~ v1_funct_2(D_2714,u1_struct_0(A_2715),'#skF_4')
      | ~ v1_funct_1(D_2714)
      | ~ l1_pre_topc(A_2715)
      | ~ v2_pre_topc(A_2715) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_54116,c_54116,c_54116,c_54116,c_54311])).

tff(c_56116,plain,(
    ! [D_2841,A_2842] :
      ( v5_pre_topc(D_2841,A_2842,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc(D_2841,A_2842,'#skF_2')
      | ~ m1_subset_1(D_2841,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2842),'#skF_4')))
      | ~ v1_funct_2(D_2841,u1_struct_0(A_2842),'#skF_4')
      | ~ m1_subset_1(D_2841,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2842),'#skF_4')))
      | ~ v1_funct_2(D_2841,u1_struct_0(A_2842),'#skF_4')
      | ~ v1_funct_1(D_2841)
      | ~ l1_pre_topc(A_2842)
      | ~ v2_pre_topc(A_2842) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55898,c_55898,c_54315])).

tff(c_56118,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_55905,c_56116])).

tff(c_56130,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_55902,c_55905,c_56118])).

tff(c_56131,plain,
    ( ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54400,c_56130])).

tff(c_56168,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56159,c_56131])).

tff(c_56169,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_56168])).

tff(c_56174,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_56169])).

tff(c_56178,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_56174])).

tff(c_56179,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_56168])).

tff(c_56183,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_120,c_56179])).

tff(c_56187,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_56183])).

tff(c_56188,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_54211])).

tff(c_56193,plain,(
    k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56188,c_54229])).

tff(c_56590,plain,(
    ! [B_2868,A_2869,C_2870] :
      ( B_2868 = '#skF_4'
      | k1_relset_1(A_2869,B_2868,C_2870) = A_2869
      | ~ v1_funct_2(C_2870,A_2869,B_2868)
      | ~ m1_subset_1(C_2870,k1_zfmisc_1(k2_zfmisc_1(A_2869,B_2868))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54105,c_32])).

tff(c_56602,plain,
    ( u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) = '#skF_4'
    | k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))),'#skF_4') = u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))) ),
    inference(resolution,[status(thm)],[c_54129,c_56590])).

tff(c_56613,plain,
    ( u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) = '#skF_4'
    | u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54114,c_56193,c_56602])).

tff(c_56633,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_56613])).

tff(c_56203,plain,(
    ! [A_78] :
      ( k1_relat_1('#skF_4') = A_78
      | ~ r1_tarski(A_78,'#skF_4')
      | ~ v4_relat_1('#skF_4',A_78)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56188,c_115])).

tff(c_56310,plain,(
    ! [A_2851] :
      ( A_2851 = '#skF_4'
      | ~ r1_tarski(A_2851,'#skF_4')
      | ~ v4_relat_1('#skF_4',A_2851) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_56188,c_56203])).

tff(c_56335,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = '#skF_4'
    | ~ r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4') ),
    inference(resolution,[status(thm)],[c_143,c_56310])).

tff(c_56561,plain,(
    ~ r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_56335])).

tff(c_56634,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56633,c_56561])).

tff(c_56643,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_56634])).

tff(c_56645,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_56613])).

tff(c_27322,plain,(
    ! [B_1416] :
      ( k1_relset_1(B_1416,u1_struct_0('#skF_2'),'#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_1416) ) ),
    inference(resolution,[status(thm)],[c_27258,c_18])).

tff(c_27326,plain,(
    ! [A_3] :
      ( k1_relset_1(A_3,u1_struct_0('#skF_2'),'#skF_4') = k1_relat_1('#skF_4')
      | ~ v4_relat_1('#skF_4',A_3)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_10,c_27322])).

tff(c_27333,plain,(
    ! [A_3] :
      ( k1_relset_1(A_3,u1_struct_0('#skF_2'),'#skF_4') = k1_relat_1('#skF_4')
      | ~ v4_relat_1('#skF_4',A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_27326])).

tff(c_53840,plain,(
    ! [A_3] :
      ( k1_relset_1(A_3,k1_xboole_0,'#skF_4') = k1_relat_1('#skF_4')
      | ~ v4_relat_1('#skF_4',A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53818,c_27333])).

tff(c_56358,plain,(
    ! [A_2853] :
      ( k1_relset_1(A_2853,'#skF_4','#skF_4') = '#skF_4'
      | ~ v4_relat_1('#skF_4',A_2853) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56188,c_54105,c_53840])).

tff(c_56381,plain,(
    k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_143,c_56358])).

tff(c_56644,plain,(
    u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_56613])).

tff(c_56475,plain,
    ( u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) = '#skF_4'
    | k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))),'#skF_4') = u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54116,c_54105,c_54116,c_34743])).

tff(c_56476,plain,(
    k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))),'#skF_4') = u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_56475])).

tff(c_56798,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56381,c_56644,c_56476])).

tff(c_56799,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56645,c_56798])).

tff(c_56800,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_56335])).

tff(c_56853,plain,
    ( v1_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_56800,c_149])).

tff(c_56962,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_56853])).

tff(c_56965,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_120,c_56962])).

tff(c_56969,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_56965])).

tff(c_56971,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_56853])).

tff(c_56850,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_56800,c_46])).

tff(c_57022,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56971,c_56850])).

tff(c_57023,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_57022])).

tff(c_57026,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_57023])).

tff(c_57030,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_57026])).

tff(c_57032,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_57022])).

tff(c_27334,plain,(
    k1_relset_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'),'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_27322])).

tff(c_53842,plain,(
    k1_relset_1(k1_relat_1('#skF_4'),k1_xboole_0,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53818,c_27334])).

tff(c_54299,plain,(
    k1_relset_1(k1_relat_1('#skF_4'),'#skF_4','#skF_4') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54105,c_53842])).

tff(c_56190,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56188,c_56188,c_54299])).

tff(c_56276,plain,(
    ! [B_1408] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_1408,'#skF_4')))
      | ~ r1_tarski('#skF_4',B_1408) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56188,c_54105,c_53844])).

tff(c_56510,plain,(
    ! [C_2863,B_2864] :
      ( v1_funct_2(C_2863,'#skF_4',B_2864)
      | k1_relset_1('#skF_4',B_2864,C_2863) != '#skF_4'
      | ~ m1_subset_1(C_2863,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_2864))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54105,c_54105,c_54105,c_54105,c_26])).

tff(c_56518,plain,
    ( v1_funct_2('#skF_4','#skF_4','#skF_4')
    | k1_relset_1('#skF_4','#skF_4','#skF_4') != '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_56276,c_56510])).

tff(c_56524,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_56190,c_56518])).

tff(c_56805,plain,(
    v1_funct_2('#skF_4','#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56800,c_54114])).

tff(c_56394,plain,(
    ! [B_1408] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_1408,u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))))
      | ~ r1_tarski('#skF_4',B_1408) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56188,c_54105,c_53841])).

tff(c_54247,plain,(
    ! [D_2711,A_2712,B_2713] :
      ( v5_pre_topc(D_2711,A_2712,B_2713)
      | ~ v5_pre_topc(D_2711,A_2712,g1_pre_topc(u1_struct_0(B_2713),u1_pre_topc(B_2713)))
      | ~ m1_subset_1(D_2711,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2712),u1_struct_0(g1_pre_topc(u1_struct_0(B_2713),u1_pre_topc(B_2713))))))
      | ~ v1_funct_2(D_2711,u1_struct_0(A_2712),u1_struct_0(g1_pre_topc(u1_struct_0(B_2713),u1_pre_topc(B_2713))))
      | ~ m1_subset_1(D_2711,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2712),u1_struct_0(B_2713))))
      | ~ v1_funct_2(D_2711,u1_struct_0(A_2712),u1_struct_0(B_2713))
      | ~ v1_funct_1(D_2711)
      | ~ l1_pre_topc(B_2713)
      | ~ v2_pre_topc(B_2713)
      | ~ l1_pre_topc(A_2712)
      | ~ v2_pre_topc(A_2712) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_54253,plain,(
    ! [D_2711,A_2712] :
      ( v5_pre_topc(D_2711,A_2712,'#skF_2')
      | ~ v5_pre_topc(D_2711,A_2712,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ m1_subset_1(D_2711,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2712),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))))
      | ~ v1_funct_2(D_2711,u1_struct_0(A_2712),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1(D_2711,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2712),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_2711,u1_struct_0(A_2712),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_2711)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_2712)
      | ~ v2_pre_topc(A_2712) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54116,c_54247])).

tff(c_57592,plain,(
    ! [D_2934,A_2935] :
      ( v5_pre_topc(D_2934,A_2935,'#skF_2')
      | ~ v5_pre_topc(D_2934,A_2935,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ m1_subset_1(D_2934,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2935),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))))
      | ~ v1_funct_2(D_2934,u1_struct_0(A_2935),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1(D_2934,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2935),'#skF_4')))
      | ~ v1_funct_2(D_2934,u1_struct_0(A_2935),'#skF_4')
      | ~ v1_funct_1(D_2934)
      | ~ l1_pre_topc(A_2935)
      | ~ v2_pre_topc(A_2935) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_54116,c_54116,c_54116,c_54116,c_54253])).

tff(c_57599,plain,(
    ! [A_2935] :
      ( v5_pre_topc('#skF_4',A_2935,'#skF_2')
      | ~ v5_pre_topc('#skF_4',A_2935,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_2935),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2935),'#skF_4')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_2935),'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(A_2935)
      | ~ v2_pre_topc(A_2935)
      | ~ r1_tarski('#skF_4',u1_struct_0(A_2935)) ) ),
    inference(resolution,[status(thm)],[c_56394,c_57592])).

tff(c_57610,plain,(
    ! [A_2936] :
      ( v5_pre_topc('#skF_4',A_2936,'#skF_2')
      | ~ v5_pre_topc('#skF_4',A_2936,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_2936),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2936),'#skF_4')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_2936),'#skF_4')
      | ~ l1_pre_topc(A_2936)
      | ~ v2_pre_topc(A_2936)
      | ~ r1_tarski('#skF_4',u1_struct_0(A_2936)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_57599])).

tff(c_57619,plain,
    ( v5_pre_topc('#skF_4','#skF_2','#skF_2')
    | ~ v5_pre_topc('#skF_4','#skF_2',g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ v1_funct_2('#skF_4','#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),'#skF_4')))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),'#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | ~ r1_tarski('#skF_4',u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_54116,c_57610])).

tff(c_57624,plain,
    ( v5_pre_topc('#skF_4','#skF_2','#skF_2')
    | ~ v5_pre_topc('#skF_4','#skF_2',g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_54116,c_74,c_72,c_56524,c_54116,c_54116,c_56805,c_57619])).

tff(c_57625,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_57624])).

tff(c_57628,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_56276,c_57625])).

tff(c_57632,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_57628])).

tff(c_57634,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_57624])).

tff(c_57512,plain,(
    ! [D_2926,A_2927] :
      ( v5_pre_topc(D_2926,g1_pre_topc(u1_struct_0(A_2927),u1_pre_topc(A_2927)),'#skF_2')
      | ~ v5_pre_topc(D_2926,A_2927,'#skF_2')
      | ~ m1_subset_1(D_2926,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2927),u1_pre_topc(A_2927))),'#skF_4')))
      | ~ v1_funct_2(D_2926,u1_struct_0(g1_pre_topc(u1_struct_0(A_2927),u1_pre_topc(A_2927))),'#skF_4')
      | ~ m1_subset_1(D_2926,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2927),'#skF_4')))
      | ~ v1_funct_2(D_2926,u1_struct_0(A_2927),'#skF_4')
      | ~ v1_funct_1(D_2926)
      | ~ l1_pre_topc(A_2927)
      | ~ v2_pre_topc(A_2927) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54105,c_54105,c_54105,c_54105,c_53897])).

tff(c_57522,plain,(
    ! [A_2927] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_2927),u1_pre_topc(A_2927)),'#skF_2')
      | ~ v5_pre_topc('#skF_4',A_2927,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_2927),u1_pre_topc(A_2927))),'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2927),'#skF_4')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_2927),'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(A_2927)
      | ~ v2_pre_topc(A_2927)
      | ~ r1_tarski('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_2927),u1_pre_topc(A_2927)))) ) ),
    inference(resolution,[status(thm)],[c_56276,c_57512])).

tff(c_57562,plain,(
    ! [A_2933] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_2933),u1_pre_topc(A_2933)),'#skF_2')
      | ~ v5_pre_topc('#skF_4',A_2933,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_2933),u1_pre_topc(A_2933))),'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2933),'#skF_4')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_2933),'#skF_4')
      | ~ l1_pre_topc(A_2933)
      | ~ v2_pre_topc(A_2933)
      | ~ r1_tarski('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_2933),u1_pre_topc(A_2933)))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_57522])).

tff(c_57568,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_4','#skF_4','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),'#skF_4')))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ r1_tarski('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_56800,c_57562])).

tff(c_57581,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_56800,c_78,c_76,c_54113,c_54107,c_56524,c_27217,c_57568])).

tff(c_56225,plain,(
    ! [D_2845,A_2846,B_2847] :
      ( v5_pre_topc(D_2845,A_2846,g1_pre_topc(u1_struct_0(B_2847),u1_pre_topc(B_2847)))
      | ~ v5_pre_topc(D_2845,A_2846,B_2847)
      | ~ m1_subset_1(D_2845,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2846),u1_struct_0(g1_pre_topc(u1_struct_0(B_2847),u1_pre_topc(B_2847))))))
      | ~ v1_funct_2(D_2845,u1_struct_0(A_2846),u1_struct_0(g1_pre_topc(u1_struct_0(B_2847),u1_pre_topc(B_2847))))
      | ~ m1_subset_1(D_2845,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2846),u1_struct_0(B_2847))))
      | ~ v1_funct_2(D_2845,u1_struct_0(A_2846),u1_struct_0(B_2847))
      | ~ v1_funct_1(D_2845)
      | ~ l1_pre_topc(B_2847)
      | ~ v2_pre_topc(B_2847)
      | ~ l1_pre_topc(A_2846)
      | ~ v2_pre_topc(A_2846) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_56231,plain,(
    ! [D_2845,A_2846] :
      ( v5_pre_topc(D_2845,A_2846,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc(D_2845,A_2846,'#skF_2')
      | ~ m1_subset_1(D_2845,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2846),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))))
      | ~ v1_funct_2(D_2845,u1_struct_0(A_2846),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1(D_2845,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2846),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_2845,u1_struct_0(A_2846),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_2845)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_2846)
      | ~ v2_pre_topc(A_2846) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54116,c_56225])).

tff(c_57776,plain,(
    ! [D_2943,A_2944] :
      ( v5_pre_topc(D_2943,A_2944,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc(D_2943,A_2944,'#skF_2')
      | ~ m1_subset_1(D_2943,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2944),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))))
      | ~ v1_funct_2(D_2943,u1_struct_0(A_2944),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1(D_2943,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2944),'#skF_4')))
      | ~ v1_funct_2(D_2943,u1_struct_0(A_2944),'#skF_4')
      | ~ v1_funct_1(D_2943)
      | ~ l1_pre_topc(A_2944)
      | ~ v2_pre_topc(A_2944) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_54116,c_54116,c_54116,c_54116,c_56231])).

tff(c_57783,plain,(
    ! [A_2944] :
      ( v5_pre_topc('#skF_4',A_2944,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc('#skF_4',A_2944,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_2944),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2944),'#skF_4')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_2944),'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(A_2944)
      | ~ v2_pre_topc(A_2944)
      | ~ r1_tarski('#skF_4',u1_struct_0(A_2944)) ) ),
    inference(resolution,[status(thm)],[c_56394,c_57776])).

tff(c_57794,plain,(
    ! [A_2945] :
      ( v5_pre_topc('#skF_4',A_2945,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc('#skF_4',A_2945,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_2945),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2945),'#skF_4')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_2945),'#skF_4')
      | ~ l1_pre_topc(A_2945)
      | ~ v2_pre_topc(A_2945)
      | ~ r1_tarski('#skF_4',u1_struct_0(A_2945)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_57783])).

tff(c_57800,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ v1_funct_2('#skF_4','#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ r1_tarski('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_56800,c_57794])).

tff(c_57806,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_56800,c_57032,c_56971,c_56524,c_56800,c_57634,c_56800,c_56805,c_57581,c_57800])).

tff(c_57808,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56387,c_57806])).

tff(c_57809,plain,(
    u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_56475])).

tff(c_57813,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57809,c_54114])).

tff(c_54132,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54129,c_52])).

tff(c_54152,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
    | ~ l1_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_64,c_54132])).

tff(c_58061,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54110,c_54112,c_54113,c_57809,c_54107,c_57809,c_57813,c_57809,c_54152])).

tff(c_58062,plain,(
    ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_56387,c_58061])).

tff(c_56235,plain,(
    ! [D_2845,A_2846] :
      ( v5_pre_topc(D_2845,A_2846,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc(D_2845,A_2846,'#skF_2')
      | ~ m1_subset_1(D_2845,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2846),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))))
      | ~ v1_funct_2(D_2845,u1_struct_0(A_2846),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1(D_2845,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2846),'#skF_4')))
      | ~ v1_funct_2(D_2845,u1_struct_0(A_2846),'#skF_4')
      | ~ v1_funct_1(D_2845)
      | ~ l1_pre_topc(A_2846)
      | ~ v2_pre_topc(A_2846) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_54116,c_54116,c_54116,c_54116,c_56231])).

tff(c_58074,plain,(
    ! [D_2967,A_2968] :
      ( v5_pre_topc(D_2967,A_2968,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc(D_2967,A_2968,'#skF_2')
      | ~ m1_subset_1(D_2967,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2968),'#skF_4')))
      | ~ v1_funct_2(D_2967,u1_struct_0(A_2968),'#skF_4')
      | ~ m1_subset_1(D_2967,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2968),'#skF_4')))
      | ~ v1_funct_2(D_2967,u1_struct_0(A_2968),'#skF_4')
      | ~ v1_funct_1(D_2967)
      | ~ l1_pre_topc(A_2968)
      | ~ v2_pre_topc(A_2968) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57809,c_57809,c_56235])).

tff(c_58083,plain,
    ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),'#skF_4')))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54107,c_58074])).

tff(c_58097,plain,(
    v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_64,c_54113,c_54107,c_27217,c_58083])).

tff(c_58099,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58062,c_58097])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:09:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.99/8.86  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.82/9.27  
% 16.82/9.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.82/9.27  %$ v5_pre_topc > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_pre_topc > v1_relat_1 > v1_pre_topc > v1_funct_1 > l1_pre_topc > k1_relset_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 16.82/9.27  
% 16.82/9.27  %Foreground sorts:
% 16.82/9.27  
% 16.82/9.27  
% 16.82/9.27  %Background operators:
% 16.82/9.27  
% 16.82/9.27  
% 16.82/9.27  %Foreground operators:
% 16.82/9.27  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 16.82/9.27  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 16.82/9.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.82/9.27  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 16.82/9.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 16.82/9.27  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 16.82/9.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.82/9.27  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 16.82/9.27  tff('#skF_2', type, '#skF_2': $i).
% 16.82/9.27  tff('#skF_3', type, '#skF_3': $i).
% 16.82/9.27  tff('#skF_1', type, '#skF_1': $i).
% 16.82/9.27  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 16.82/9.27  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 16.82/9.27  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 16.82/9.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 16.82/9.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.82/9.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 16.82/9.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 16.82/9.27  tff('#skF_4', type, '#skF_4': $i).
% 16.82/9.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.82/9.27  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 16.82/9.27  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 16.82/9.27  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 16.82/9.27  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 16.82/9.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 16.82/9.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 16.82/9.27  
% 17.05/9.36  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 17.05/9.36  tff(f_193, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))), u1_struct_0(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))), u1_struct_0(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))) => ((C = D) => (v5_pre_topc(C, A, B) <=> v5_pre_topc(D, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)), g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_pre_topc)).
% 17.05/9.36  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 17.05/9.36  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 17.05/9.36  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 17.05/9.36  tff(f_57, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 17.05/9.36  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 17.05/9.36  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 17.05/9.36  tff(f_134, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))), u1_struct_0(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))), u1_struct_0(B))))) => ((C = D) => (v5_pre_topc(C, A, B) <=> v5_pre_topc(D, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)), B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_pre_topc)).
% 17.05/9.36  tff(f_105, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & v2_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_pre_topc)).
% 17.05/9.36  tff(f_97, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 17.05/9.36  tff(f_93, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v1_pre_topc(g1_pre_topc(A, B)) & l1_pre_topc(g1_pre_topc(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 17.05/9.36  tff(f_163, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(A), u1_struct_0(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))) => ((C = D) => (v5_pre_topc(C, A, B) <=> v5_pre_topc(D, A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_pre_topc)).
% 17.05/9.36  tff(f_87, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((k1_relset_1(A, B, C) = A) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_funct_2)).
% 17.05/9.36  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 17.05/9.36  tff(c_58, plain, ('#skF_3'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_193])).
% 17.05/9.36  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_193])).
% 17.05/9.36  tff(c_91, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_66])).
% 17.05/9.36  tff(c_106, plain, (![C_72, A_73, B_74]: (v1_relat_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 17.05/9.36  tff(c_110, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_91, c_106])).
% 17.05/9.36  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))))), inference(cnfTransformation, [status(thm)], [f_193])).
% 17.05/9.36  tff(c_136, plain, (![C_84, A_85, B_86]: (v4_relat_1(C_84, A_85) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 17.05/9.36  tff(c_143, plain, (v4_relat_1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(resolution, [status(thm)], [c_60, c_136])).
% 17.05/9.36  tff(c_10, plain, (![B_4, A_3]: (r1_tarski(k1_relat_1(B_4), A_3) | ~v4_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 17.05/9.36  tff(c_78, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_193])).
% 17.05/9.36  tff(c_76, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_193])).
% 17.05/9.36  tff(c_27251, plain, (![D_1407, B_1408, C_1409, A_1410]: (m1_subset_1(D_1407, k1_zfmisc_1(k2_zfmisc_1(B_1408, C_1409))) | ~r1_tarski(k1_relat_1(D_1407), B_1408) | ~m1_subset_1(D_1407, k1_zfmisc_1(k2_zfmisc_1(A_1410, C_1409))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 17.05/9.36  tff(c_27258, plain, (![B_1411]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_1411, u1_struct_0('#skF_2')))) | ~r1_tarski(k1_relat_1('#skF_4'), B_1411))), inference(resolution, [status(thm)], [c_91, c_27251])).
% 17.05/9.36  tff(c_30, plain, (![B_19, C_20]: (k1_relset_1(k1_xboole_0, B_19, C_20)=k1_xboole_0 | ~v1_funct_2(C_20, k1_xboole_0, B_19) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_19))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 17.05/9.36  tff(c_27282, plain, (k1_relset_1(k1_xboole_0, u1_struct_0('#skF_2'), '#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_4', k1_xboole_0, u1_struct_0('#skF_2')) | ~r1_tarski(k1_relat_1('#skF_4'), k1_xboole_0)), inference(resolution, [status(thm)], [c_27258, c_30])).
% 17.05/9.36  tff(c_27410, plain, (~r1_tarski(k1_relat_1('#skF_4'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_27282])).
% 17.05/9.36  tff(c_27413, plain, (~v4_relat_1('#skF_4', k1_xboole_0) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_27410])).
% 17.05/9.36  tff(c_27416, plain, (~v4_relat_1('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_110, c_27413])).
% 17.05/9.36  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_193])).
% 17.05/9.36  tff(c_68, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_193])).
% 17.05/9.36  tff(c_87, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_68])).
% 17.05/9.36  tff(c_27221, plain, (![A_1396, B_1397, C_1398]: (k1_relset_1(A_1396, B_1397, C_1398)=k1_relat_1(C_1398) | ~m1_subset_1(C_1398, k1_zfmisc_1(k2_zfmisc_1(A_1396, B_1397))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 17.05/9.36  tff(c_27229, plain, (k1_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_91, c_27221])).
% 17.05/9.36  tff(c_27418, plain, (![B_1420, A_1421, C_1422]: (k1_xboole_0=B_1420 | k1_relset_1(A_1421, B_1420, C_1422)=A_1421 | ~v1_funct_2(C_1422, A_1421, B_1420) | ~m1_subset_1(C_1422, k1_zfmisc_1(k2_zfmisc_1(A_1421, B_1420))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 17.05/9.36  tff(c_27430, plain, (u1_struct_0('#skF_2')=k1_xboole_0 | k1_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4')=u1_struct_0('#skF_1') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_91, c_27418])).
% 17.05/9.36  tff(c_27438, plain, (u1_struct_0('#skF_2')=k1_xboole_0 | u1_struct_0('#skF_1')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_87, c_27229, c_27430])).
% 17.05/9.36  tff(c_27439, plain, (u1_struct_0('#skF_1')=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_27438])).
% 17.05/9.36  tff(c_86, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_193])).
% 17.05/9.36  tff(c_88, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_86])).
% 17.05/9.36  tff(c_162, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_88])).
% 17.05/9.36  tff(c_80, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_193])).
% 17.05/9.36  tff(c_90, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_80])).
% 17.05/9.36  tff(c_194, plain, (~v5_pre_topc('#skF_4', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_162, c_90])).
% 17.05/9.36  tff(c_144, plain, (v4_relat_1('#skF_4', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_91, c_136])).
% 17.05/9.36  tff(c_195, plain, (![D_106, B_107, C_108, A_109]: (m1_subset_1(D_106, k1_zfmisc_1(k2_zfmisc_1(B_107, C_108))) | ~r1_tarski(k1_relat_1(D_106), B_107) | ~m1_subset_1(D_106, k1_zfmisc_1(k2_zfmisc_1(A_109, C_108))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 17.05/9.36  tff(c_202, plain, (![B_110]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_110, u1_struct_0('#skF_2')))) | ~r1_tarski(k1_relat_1('#skF_4'), B_110))), inference(resolution, [status(thm)], [c_91, c_195])).
% 17.05/9.36  tff(c_227, plain, (k1_relset_1(k1_xboole_0, u1_struct_0('#skF_2'), '#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_4', k1_xboole_0, u1_struct_0('#skF_2')) | ~r1_tarski(k1_relat_1('#skF_4'), k1_xboole_0)), inference(resolution, [status(thm)], [c_202, c_30])).
% 17.05/9.36  tff(c_369, plain, (~r1_tarski(k1_relat_1('#skF_4'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_227])).
% 17.05/9.36  tff(c_372, plain, (~v4_relat_1('#skF_4', k1_xboole_0) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_369])).
% 17.05/9.36  tff(c_375, plain, (~v4_relat_1('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_110, c_372])).
% 17.05/9.36  tff(c_165, plain, (![A_95, B_96, C_97]: (k1_relset_1(A_95, B_96, C_97)=k1_relat_1(C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 17.05/9.36  tff(c_173, plain, (k1_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_91, c_165])).
% 17.05/9.36  tff(c_413, plain, (![B_125, A_126, C_127]: (k1_xboole_0=B_125 | k1_relset_1(A_126, B_125, C_127)=A_126 | ~v1_funct_2(C_127, A_126, B_125) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_126, B_125))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 17.05/9.36  tff(c_425, plain, (u1_struct_0('#skF_2')=k1_xboole_0 | k1_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4')=u1_struct_0('#skF_1') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_91, c_413])).
% 17.05/9.36  tff(c_433, plain, (u1_struct_0('#skF_2')=k1_xboole_0 | u1_struct_0('#skF_1')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_87, c_173, c_425])).
% 17.05/9.36  tff(c_3860, plain, (u1_struct_0('#skF_1')=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_433])).
% 17.05/9.36  tff(c_3869, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3860, c_87])).
% 17.05/9.36  tff(c_74, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_193])).
% 17.05/9.36  tff(c_72, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_193])).
% 17.05/9.36  tff(c_435, plain, (u1_struct_0('#skF_1')=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_433])).
% 17.05/9.36  tff(c_444, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_435, c_87])).
% 17.05/9.36  tff(c_442, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_435, c_91])).
% 17.05/9.36  tff(c_62, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_193])).
% 17.05/9.36  tff(c_172, plain, (k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_165])).
% 17.05/9.36  tff(c_422, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0 | k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')=u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(resolution, [status(thm)], [c_60, c_413])).
% 17.05/9.36  tff(c_430, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0 | u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_172, c_422])).
% 17.05/9.36  tff(c_434, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_430])).
% 17.05/9.36  tff(c_540, plain, (u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_435, c_434])).
% 17.05/9.36  tff(c_1690, plain, (![D_200, A_201, B_202]: (v5_pre_topc(D_200, A_201, B_202) | ~v5_pre_topc(D_200, g1_pre_topc(u1_struct_0(A_201), u1_pre_topc(A_201)), B_202) | ~m1_subset_1(D_200, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_201), u1_pre_topc(A_201))), u1_struct_0(B_202)))) | ~v1_funct_2(D_200, u1_struct_0(g1_pre_topc(u1_struct_0(A_201), u1_pre_topc(A_201))), u1_struct_0(B_202)) | ~m1_subset_1(D_200, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_201), u1_struct_0(B_202)))) | ~v1_funct_2(D_200, u1_struct_0(A_201), u1_struct_0(B_202)) | ~v1_funct_1(D_200) | ~l1_pre_topc(B_202) | ~v2_pre_topc(B_202) | ~l1_pre_topc(A_201) | ~v2_pre_topc(A_201))), inference(cnfTransformation, [status(thm)], [f_134])).
% 17.05/9.36  tff(c_1699, plain, (![D_200, B_202]: (v5_pre_topc(D_200, '#skF_1', B_202) | ~v5_pre_topc(D_200, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_202) | ~m1_subset_1(D_200, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(B_202)))) | ~v1_funct_2(D_200, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_202)) | ~m1_subset_1(D_200, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_202)))) | ~v1_funct_2(D_200, u1_struct_0('#skF_1'), u1_struct_0(B_202)) | ~v1_funct_1(D_200) | ~l1_pre_topc(B_202) | ~v2_pre_topc(B_202) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_435, c_1690])).
% 17.05/9.36  tff(c_2476, plain, (![D_242, B_243]: (v5_pre_topc(D_242, '#skF_1', B_243) | ~v5_pre_topc(D_242, g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), B_243) | ~m1_subset_1(D_242, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_243)))) | ~v1_funct_2(D_242, k1_relat_1('#skF_4'), u1_struct_0(B_243)) | ~v1_funct_1(D_242) | ~l1_pre_topc(B_243) | ~v2_pre_topc(B_243))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_435, c_435, c_540, c_435, c_540, c_435, c_1699])).
% 17.05/9.36  tff(c_2485, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), '#skF_2') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_442, c_2476])).
% 17.05/9.36  tff(c_2504, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_64, c_444, c_2485])).
% 17.05/9.36  tff(c_2505, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_194, c_2504])).
% 17.05/9.36  tff(c_46, plain, (![A_27]: (v2_pre_topc(g1_pre_topc(u1_struct_0(A_27), u1_pre_topc(A_27))) | ~l1_pre_topc(A_27) | ~v2_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_105])).
% 17.05/9.36  tff(c_450, plain, (v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_435, c_46])).
% 17.05/9.36  tff(c_463, plain, (v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_450])).
% 17.05/9.36  tff(c_116, plain, (![A_79]: (m1_subset_1(u1_pre_topc(A_79), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_79)))) | ~l1_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_97])).
% 17.05/9.36  tff(c_40, plain, (![A_24, B_25]: (l1_pre_topc(g1_pre_topc(A_24, B_25)) | ~m1_subset_1(B_25, k1_zfmisc_1(k1_zfmisc_1(A_24))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 17.05/9.36  tff(c_120, plain, (![A_79]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_79), u1_pre_topc(A_79))) | ~l1_pre_topc(A_79))), inference(resolution, [status(thm)], [c_116, c_40])).
% 17.05/9.36  tff(c_456, plain, (l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_435, c_120])).
% 17.05/9.36  tff(c_467, plain, (l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_456])).
% 17.05/9.36  tff(c_443, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_435, c_62])).
% 17.05/9.36  tff(c_542, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_540, c_443])).
% 17.05/9.36  tff(c_437, plain, (v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_435, c_162])).
% 17.05/9.36  tff(c_200, plain, (![B_107]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_107, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))))) | ~r1_tarski(k1_relat_1('#skF_4'), B_107))), inference(resolution, [status(thm)], [c_60, c_195])).
% 17.05/9.36  tff(c_471, plain, (![D_128, A_129, B_130]: (v5_pre_topc(D_128, A_129, B_130) | ~v5_pre_topc(D_128, A_129, g1_pre_topc(u1_struct_0(B_130), u1_pre_topc(B_130))) | ~m1_subset_1(D_128, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_129), u1_struct_0(g1_pre_topc(u1_struct_0(B_130), u1_pre_topc(B_130)))))) | ~v1_funct_2(D_128, u1_struct_0(A_129), u1_struct_0(g1_pre_topc(u1_struct_0(B_130), u1_pre_topc(B_130)))) | ~m1_subset_1(D_128, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_129), u1_struct_0(B_130)))) | ~v1_funct_2(D_128, u1_struct_0(A_129), u1_struct_0(B_130)) | ~v1_funct_1(D_128) | ~l1_pre_topc(B_130) | ~v2_pre_topc(B_130) | ~l1_pre_topc(A_129) | ~v2_pre_topc(A_129))), inference(cnfTransformation, [status(thm)], [f_163])).
% 17.05/9.36  tff(c_481, plain, (![A_129]: (v5_pre_topc('#skF_4', A_129, '#skF_2') | ~v5_pre_topc('#skF_4', A_129, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_129), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_129), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0(A_129), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(A_129) | ~v2_pre_topc(A_129) | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(A_129)))), inference(resolution, [status(thm)], [c_200, c_471])).
% 17.05/9.36  tff(c_2551, plain, (![A_247]: (v5_pre_topc('#skF_4', A_247, '#skF_2') | ~v5_pre_topc('#skF_4', A_247, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_247), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_247), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0(A_247), u1_struct_0('#skF_2')) | ~l1_pre_topc(A_247) | ~v2_pre_topc(A_247) | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(A_247)))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_64, c_481])).
% 17.05/9.36  tff(c_2557, plain, (v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), '#skF_2') | ~v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0('#skF_2')) | ~l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))) | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_540, c_2551])).
% 17.05/9.36  tff(c_2563, plain, (v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_540, c_463, c_467, c_444, c_540, c_442, c_540, c_542, c_437, c_2557])).
% 17.05/9.36  tff(c_2565, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2505, c_2563])).
% 17.05/9.36  tff(c_2566, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_433])).
% 17.05/9.36  tff(c_2583, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2566, c_87])).
% 17.05/9.36  tff(c_2581, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2566, c_91])).
% 17.05/9.36  tff(c_24, plain, (![C_20, A_18]: (k1_xboole_0=C_20 | ~v1_funct_2(C_20, A_18, k1_xboole_0) | k1_xboole_0=A_18 | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 17.05/9.36  tff(c_2642, plain, (k1_xboole_0='#skF_4' | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), k1_xboole_0) | u1_struct_0('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_2581, c_24])).
% 17.05/9.36  tff(c_2668, plain, (k1_xboole_0='#skF_4' | u1_struct_0('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2583, c_2642])).
% 17.05/9.36  tff(c_2676, plain, (u1_struct_0('#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2668])).
% 17.05/9.36  tff(c_2682, plain, (v4_relat_1('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2676, c_144])).
% 17.05/9.36  tff(c_2684, plain, $false, inference(negUnitSimplification, [status(thm)], [c_375, c_2682])).
% 17.05/9.36  tff(c_2685, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_2668])).
% 17.05/9.36  tff(c_2693, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2685, c_2583])).
% 17.05/9.36  tff(c_2687, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2685, c_2581])).
% 17.05/9.36  tff(c_201, plain, (![B_107]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_107, u1_struct_0('#skF_2')))) | ~r1_tarski(k1_relat_1('#skF_4'), B_107))), inference(resolution, [status(thm)], [c_91, c_195])).
% 17.05/9.36  tff(c_2575, plain, (![B_107]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_107, k1_xboole_0))) | ~r1_tarski(k1_relat_1('#skF_4'), B_107))), inference(demodulation, [status(thm), theory('equality')], [c_2566, c_201])).
% 17.05/9.36  tff(c_2969, plain, (![B_107]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_107, '#skF_4'))) | ~r1_tarski(k1_relat_1('#skF_4'), B_107))), inference(demodulation, [status(thm), theory('equality')], [c_2685, c_2575])).
% 17.05/9.36  tff(c_22, plain, (![A_18]: (v1_funct_2(k1_xboole_0, A_18, k1_xboole_0) | k1_xboole_0=A_18 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_18, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 17.05/9.36  tff(c_3090, plain, (![A_264]: (v1_funct_2('#skF_4', A_264, '#skF_4') | A_264='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_264, '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_2685, c_2685, c_2685, c_2685, c_2685, c_22])).
% 17.05/9.36  tff(c_3101, plain, (![B_265]: (v1_funct_2('#skF_4', B_265, '#skF_4') | B_265='#skF_4' | ~r1_tarski(k1_relat_1('#skF_4'), B_265))), inference(resolution, [status(thm)], [c_2969, c_3090])).
% 17.05/9.36  tff(c_3113, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_4') | k1_relat_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_6, c_3101])).
% 17.05/9.36  tff(c_3114, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(splitLeft, [status(thm)], [c_3113])).
% 17.05/9.36  tff(c_2698, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2685, c_369])).
% 17.05/9.36  tff(c_3126, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3114, c_2698])).
% 17.05/9.36  tff(c_3132, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_3126])).
% 17.05/9.36  tff(c_3133, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_3113])).
% 17.05/9.36  tff(c_2926, plain, (l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_434, c_120])).
% 17.05/9.36  tff(c_3215, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_2926])).
% 17.05/9.36  tff(c_3218, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_120, c_3215])).
% 17.05/9.36  tff(c_3222, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_3218])).
% 17.05/9.36  tff(c_3224, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_2926])).
% 17.05/9.36  tff(c_2920, plain, (v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_434, c_46])).
% 17.05/9.36  tff(c_3588, plain, (v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_3224, c_2920])).
% 17.05/9.36  tff(c_3589, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_3588])).
% 17.05/9.36  tff(c_3592, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_3589])).
% 17.05/9.36  tff(c_3596, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_3592])).
% 17.05/9.36  tff(c_3598, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_3588])).
% 17.05/9.36  tff(c_2582, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_2566, c_62])).
% 17.05/9.36  tff(c_2688, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_2685, c_2582])).
% 17.05/9.36  tff(c_2949, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_434, c_2688])).
% 17.05/9.36  tff(c_2576, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2566, c_162])).
% 17.05/9.36  tff(c_3014, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2685, c_2576])).
% 17.05/9.36  tff(c_2571, plain, (![B_107]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_107, u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2')))))) | ~r1_tarski(k1_relat_1('#skF_4'), B_107))), inference(demodulation, [status(thm), theory('equality')], [c_2566, c_200])).
% 17.05/9.36  tff(c_3047, plain, (![B_107]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_107, u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))))) | ~r1_tarski(k1_relat_1('#skF_4'), B_107))), inference(demodulation, [status(thm), theory('equality')], [c_2685, c_2571])).
% 17.05/9.36  tff(c_2608, plain, (![D_248, A_249, B_250]: (v5_pre_topc(D_248, A_249, B_250) | ~v5_pre_topc(D_248, A_249, g1_pre_topc(u1_struct_0(B_250), u1_pre_topc(B_250))) | ~m1_subset_1(D_248, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_249), u1_struct_0(g1_pre_topc(u1_struct_0(B_250), u1_pre_topc(B_250)))))) | ~v1_funct_2(D_248, u1_struct_0(A_249), u1_struct_0(g1_pre_topc(u1_struct_0(B_250), u1_pre_topc(B_250)))) | ~m1_subset_1(D_248, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_249), u1_struct_0(B_250)))) | ~v1_funct_2(D_248, u1_struct_0(A_249), u1_struct_0(B_250)) | ~v1_funct_1(D_248) | ~l1_pre_topc(B_250) | ~v2_pre_topc(B_250) | ~l1_pre_topc(A_249) | ~v2_pre_topc(A_249))), inference(cnfTransformation, [status(thm)], [f_163])).
% 17.05/9.36  tff(c_2614, plain, (![D_248, A_249]: (v5_pre_topc(D_248, A_249, '#skF_2') | ~v5_pre_topc(D_248, A_249, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_subset_1(D_248, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_249), u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2')))))) | ~v1_funct_2(D_248, u1_struct_0(A_249), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1(D_248, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_249), u1_struct_0('#skF_2')))) | ~v1_funct_2(D_248, u1_struct_0(A_249), u1_struct_0('#skF_2')) | ~v1_funct_1(D_248) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(A_249) | ~v2_pre_topc(A_249))), inference(superposition, [status(thm), theory('equality')], [c_2566, c_2608])).
% 17.05/9.36  tff(c_2618, plain, (![D_248, A_249]: (v5_pre_topc(D_248, A_249, '#skF_2') | ~v5_pre_topc(D_248, A_249, g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2'))) | ~m1_subset_1(D_248, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_249), u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2')))))) | ~v1_funct_2(D_248, u1_struct_0(A_249), u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2')))) | ~m1_subset_1(D_248, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_249), k1_xboole_0))) | ~v1_funct_2(D_248, u1_struct_0(A_249), k1_xboole_0) | ~v1_funct_1(D_248) | ~l1_pre_topc(A_249) | ~v2_pre_topc(A_249))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_2566, c_2566, c_2566, c_2566, c_2614])).
% 17.05/9.36  tff(c_3731, plain, (![D_314, A_315]: (v5_pre_topc(D_314, A_315, '#skF_2') | ~v5_pre_topc(D_314, A_315, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~m1_subset_1(D_314, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_315), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))))) | ~v1_funct_2(D_314, u1_struct_0(A_315), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~m1_subset_1(D_314, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_315), '#skF_4'))) | ~v1_funct_2(D_314, u1_struct_0(A_315), '#skF_4') | ~v1_funct_1(D_314) | ~l1_pre_topc(A_315) | ~v2_pre_topc(A_315))), inference(demodulation, [status(thm), theory('equality')], [c_2685, c_2685, c_2685, c_2685, c_2685, c_2618])).
% 17.05/9.36  tff(c_3735, plain, (![A_315]: (v5_pre_topc('#skF_4', A_315, '#skF_2') | ~v5_pre_topc('#skF_4', A_315, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_315), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_315), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_315), '#skF_4') | ~v1_funct_1('#skF_4') | ~l1_pre_topc(A_315) | ~v2_pre_topc(A_315) | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(A_315)))), inference(resolution, [status(thm)], [c_3047, c_3731])).
% 17.05/9.36  tff(c_3766, plain, (![A_318]: (v5_pre_topc('#skF_4', A_318, '#skF_2') | ~v5_pre_topc('#skF_4', A_318, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_318), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_318), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_318), '#skF_4') | ~l1_pre_topc(A_318) | ~v2_pre_topc(A_318) | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(A_318)))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_3735])).
% 17.05/9.36  tff(c_3772, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_434, c_3766])).
% 17.05/9.36  tff(c_3778, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_434, c_3598, c_3224, c_3133, c_434, c_434, c_2949, c_3014, c_3772])).
% 17.05/9.36  tff(c_3781, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_4')))), inference(splitLeft, [status(thm)], [c_3778])).
% 17.05/9.36  tff(c_3784, plain, (~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_2969, c_3781])).
% 17.05/9.36  tff(c_3788, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_3784])).
% 17.05/9.36  tff(c_3790, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_4')))), inference(splitRight, [status(thm)], [c_3778])).
% 17.05/9.36  tff(c_3789, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')), inference(splitRight, [status(thm)], [c_3778])).
% 17.05/9.36  tff(c_2695, plain, (u1_struct_0('#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2685, c_2566])).
% 17.05/9.36  tff(c_50, plain, (![D_42, A_28, B_36]: (v5_pre_topc(D_42, A_28, B_36) | ~v5_pre_topc(D_42, g1_pre_topc(u1_struct_0(A_28), u1_pre_topc(A_28)), B_36) | ~m1_subset_1(D_42, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_28), u1_pre_topc(A_28))), u1_struct_0(B_36)))) | ~v1_funct_2(D_42, u1_struct_0(g1_pre_topc(u1_struct_0(A_28), u1_pre_topc(A_28))), u1_struct_0(B_36)) | ~m1_subset_1(D_42, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_28), u1_struct_0(B_36)))) | ~v1_funct_2(D_42, u1_struct_0(A_28), u1_struct_0(B_36)) | ~v1_funct_1(D_42) | ~l1_pre_topc(B_36) | ~v2_pre_topc(B_36) | ~l1_pre_topc(A_28) | ~v2_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_134])).
% 17.05/9.36  tff(c_2905, plain, (![D_42, B_36]: (v5_pre_topc(D_42, '#skF_1', B_36) | ~v5_pre_topc(D_42, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_36) | ~m1_subset_1(D_42, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_36)))) | ~v1_funct_2(D_42, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_36)) | ~m1_subset_1(D_42, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_36)))) | ~v1_funct_2(D_42, u1_struct_0('#skF_1'), u1_struct_0(B_36)) | ~v1_funct_1(D_42) | ~l1_pre_topc(B_36) | ~v2_pre_topc(B_36) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_434, c_50])).
% 17.05/9.36  tff(c_3600, plain, (![D_302, B_303]: (v5_pre_topc(D_302, '#skF_1', B_303) | ~v5_pre_topc(D_302, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_303) | ~m1_subset_1(D_302, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_303)))) | ~v1_funct_2(D_302, k1_relat_1('#skF_4'), u1_struct_0(B_303)) | ~m1_subset_1(D_302, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_303)))) | ~v1_funct_2(D_302, u1_struct_0('#skF_1'), u1_struct_0(B_303)) | ~v1_funct_1(D_302) | ~l1_pre_topc(B_303) | ~v2_pre_topc(B_303))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_434, c_2905])).
% 17.05/9.36  tff(c_3610, plain, (![D_302]: (v5_pre_topc(D_302, '#skF_1', '#skF_2') | ~v5_pre_topc(D_302, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~m1_subset_1(D_302, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(D_302, k1_relat_1('#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(D_302, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), '#skF_4'))) | ~v1_funct_2(D_302, u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(D_302) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2695, c_3600])).
% 17.05/9.36  tff(c_3617, plain, (![D_302]: (v5_pre_topc(D_302, '#skF_1', '#skF_2') | ~v5_pre_topc(D_302, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~m1_subset_1(D_302, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_4'))) | ~v1_funct_2(D_302, k1_relat_1('#skF_4'), '#skF_4') | ~m1_subset_1(D_302, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), '#skF_4'))) | ~v1_funct_2(D_302, u1_struct_0('#skF_1'), '#skF_4') | ~v1_funct_1(D_302))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_2695, c_2695, c_2695, c_3610])).
% 17.05/9.36  tff(c_3852, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_4'))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_3789, c_3617])).
% 17.05/9.36  tff(c_3855, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2693, c_2687, c_3133, c_3790, c_3852])).
% 17.05/9.36  tff(c_3857, plain, $false, inference(negUnitSimplification, [status(thm)], [c_194, c_3855])).
% 17.05/9.36  tff(c_3858, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0), inference(splitRight, [status(thm)], [c_430])).
% 17.05/9.36  tff(c_3868, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_3860, c_62])).
% 17.05/9.36  tff(c_3921, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3858, c_3868])).
% 17.05/9.36  tff(c_3866, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))))), inference(demodulation, [status(thm), theory('equality')], [c_3860, c_60])).
% 17.05/9.36  tff(c_4082, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_3858, c_3866])).
% 17.05/9.36  tff(c_4096, plain, (k1_xboole_0='#skF_4' | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), k1_xboole_0) | u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))=k1_xboole_0), inference(resolution, [status(thm)], [c_4082, c_24])).
% 17.05/9.36  tff(c_4122, plain, (k1_xboole_0='#skF_4' | u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3921, c_4096])).
% 17.05/9.36  tff(c_4130, plain, (u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))=k1_xboole_0), inference(splitLeft, [status(thm)], [c_4122])).
% 17.05/9.36  tff(c_3864, plain, (v4_relat_1('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_3860, c_143])).
% 17.05/9.36  tff(c_4134, plain, (v4_relat_1('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4130, c_3864])).
% 17.05/9.36  tff(c_4136, plain, $false, inference(negUnitSimplification, [status(thm)], [c_375, c_4134])).
% 17.05/9.36  tff(c_4137, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_4122])).
% 17.05/9.36  tff(c_3923, plain, (![B_107]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_107, k1_xboole_0))) | ~r1_tarski(k1_relat_1('#skF_4'), B_107))), inference(demodulation, [status(thm), theory('equality')], [c_3858, c_200])).
% 17.05/9.36  tff(c_4140, plain, (![B_107]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_107, '#skF_4'))) | ~r1_tarski(k1_relat_1('#skF_4'), B_107))), inference(demodulation, [status(thm), theory('equality')], [c_4137, c_3923])).
% 17.05/9.36  tff(c_4362, plain, (![A_335]: (v1_funct_2('#skF_4', A_335, '#skF_4') | A_335='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_335, '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_4137, c_4137, c_4137, c_4137, c_4137, c_22])).
% 17.05/9.36  tff(c_4373, plain, (![B_336]: (v1_funct_2('#skF_4', B_336, '#skF_4') | B_336='#skF_4' | ~r1_tarski(k1_relat_1('#skF_4'), B_336))), inference(resolution, [status(thm)], [c_4140, c_4362])).
% 17.05/9.36  tff(c_4385, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_4') | k1_relat_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_6, c_4373])).
% 17.05/9.36  tff(c_4386, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(splitLeft, [status(thm)], [c_4385])).
% 17.05/9.36  tff(c_4146, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4137, c_369])).
% 17.05/9.36  tff(c_4414, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4386, c_4146])).
% 17.05/9.36  tff(c_4433, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_4414])).
% 17.05/9.36  tff(c_4434, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_4385])).
% 17.05/9.36  tff(c_4141, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4137, c_3921])).
% 17.05/9.36  tff(c_3862, plain, (v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_3860, c_162])).
% 17.05/9.36  tff(c_44, plain, (![A_26]: (m1_subset_1(u1_pre_topc(A_26), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_26)))) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_97])).
% 17.05/9.36  tff(c_145, plain, (![A_87, B_88]: (v1_pre_topc(g1_pre_topc(A_87, B_88)) | ~m1_subset_1(B_88, k1_zfmisc_1(k1_zfmisc_1(A_87))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 17.05/9.36  tff(c_149, plain, (![A_26]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_26), u1_pre_topc(A_26))) | ~l1_pre_topc(A_26))), inference(resolution, [status(thm)], [c_44, c_145])).
% 17.05/9.36  tff(c_3940, plain, (v1_pre_topc(g1_pre_topc(k1_xboole_0, u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_3858, c_149])).
% 17.05/9.36  tff(c_4469, plain, (v1_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_4137, c_3940])).
% 17.05/9.36  tff(c_4470, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_4469])).
% 17.05/9.36  tff(c_4473, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_120, c_4470])).
% 17.05/9.36  tff(c_4477, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_4473])).
% 17.05/9.36  tff(c_4479, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_4469])).
% 17.05/9.36  tff(c_3937, plain, (v2_pre_topc(g1_pre_topc(k1_xboole_0, u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_3858, c_46])).
% 17.05/9.36  tff(c_5048, plain, (v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_4479, c_4137, c_3937])).
% 17.05/9.36  tff(c_5049, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_5048])).
% 17.05/9.36  tff(c_5052, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_46, c_5049])).
% 17.05/9.36  tff(c_5056, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_5052])).
% 17.05/9.36  tff(c_5058, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_5048])).
% 17.05/9.36  tff(c_4143, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4137, c_3858])).
% 17.05/9.36  tff(c_3896, plain, (![D_319, A_320, B_321]: (v5_pre_topc(D_319, A_320, B_321) | ~v5_pre_topc(D_319, g1_pre_topc(u1_struct_0(A_320), u1_pre_topc(A_320)), B_321) | ~m1_subset_1(D_319, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_320), u1_pre_topc(A_320))), u1_struct_0(B_321)))) | ~v1_funct_2(D_319, u1_struct_0(g1_pre_topc(u1_struct_0(A_320), u1_pre_topc(A_320))), u1_struct_0(B_321)) | ~m1_subset_1(D_319, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_320), u1_struct_0(B_321)))) | ~v1_funct_2(D_319, u1_struct_0(A_320), u1_struct_0(B_321)) | ~v1_funct_1(D_319) | ~l1_pre_topc(B_321) | ~v2_pre_topc(B_321) | ~l1_pre_topc(A_320) | ~v2_pre_topc(A_320))), inference(cnfTransformation, [status(thm)], [f_134])).
% 17.05/9.36  tff(c_3906, plain, (![A_320]: (v5_pre_topc('#skF_4', A_320, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_320), u1_pre_topc(A_320)), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_320), u1_pre_topc(A_320))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_320), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))))) | ~v1_funct_2('#skF_4', u1_struct_0(A_320), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_320) | ~v2_pre_topc(A_320) | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0(A_320), u1_pre_topc(A_320)))))), inference(resolution, [status(thm)], [c_200, c_3896])).
% 17.05/9.36  tff(c_3917, plain, (![A_320]: (v5_pre_topc('#skF_4', A_320, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_320), u1_pre_topc(A_320)), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_320), u1_pre_topc(A_320))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_320), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))))) | ~v1_funct_2('#skF_4', u1_struct_0(A_320), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_320) | ~v2_pre_topc(A_320) | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0(A_320), u1_pre_topc(A_320)))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_3906])).
% 17.05/9.36  tff(c_5125, plain, (![A_378]: (v5_pre_topc('#skF_4', A_378, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_378), u1_pre_topc(A_378)), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_378), u1_pre_topc(A_378))), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_378), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_378), '#skF_4') | ~l1_pre_topc(A_378) | ~v2_pre_topc(A_378) | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0(A_378), u1_pre_topc(A_378)))))), inference(demodulation, [status(thm), theory('equality')], [c_5058, c_4479, c_4143, c_4143, c_4143, c_3917])).
% 17.05/9.36  tff(c_5134, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_3860, c_5125])).
% 17.05/9.36  tff(c_5139, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_4'))) | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_3860, c_78, c_76, c_4434, c_3860, c_3860, c_4141, c_3860, c_3862, c_5134])).
% 17.05/9.36  tff(c_5140, plain, (~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))))), inference(splitLeft, [status(thm)], [c_5139])).
% 17.05/9.36  tff(c_5143, plain, (~v4_relat_1('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_5140])).
% 17.05/9.36  tff(c_5147, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_110, c_3864, c_5143])).
% 17.05/9.36  tff(c_5148, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_4'))) | v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_5139])).
% 17.05/9.36  tff(c_5223, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_4')))), inference(splitLeft, [status(thm)], [c_5148])).
% 17.05/9.36  tff(c_5226, plain, (~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_4140, c_5223])).
% 17.05/9.36  tff(c_5230, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_5226])).
% 17.05/9.36  tff(c_5232, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_4')))), inference(splitRight, [status(thm)], [c_5148])).
% 17.05/9.36  tff(c_5231, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_5148])).
% 17.05/9.36  tff(c_54, plain, (![D_57, A_43, B_51]: (v5_pre_topc(D_57, A_43, B_51) | ~v5_pre_topc(D_57, A_43, g1_pre_topc(u1_struct_0(B_51), u1_pre_topc(B_51))) | ~m1_subset_1(D_57, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_43), u1_struct_0(g1_pre_topc(u1_struct_0(B_51), u1_pre_topc(B_51)))))) | ~v1_funct_2(D_57, u1_struct_0(A_43), u1_struct_0(g1_pre_topc(u1_struct_0(B_51), u1_pre_topc(B_51)))) | ~m1_subset_1(D_57, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_43), u1_struct_0(B_51)))) | ~v1_funct_2(D_57, u1_struct_0(A_43), u1_struct_0(B_51)) | ~v1_funct_1(D_57) | ~l1_pre_topc(B_51) | ~v2_pre_topc(B_51) | ~l1_pre_topc(A_43) | ~v2_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_163])).
% 17.05/9.36  tff(c_4183, plain, (![D_57, A_43]: (v5_pre_topc(D_57, A_43, '#skF_2') | ~v5_pre_topc(D_57, A_43, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_subset_1(D_57, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_43), '#skF_4'))) | ~v1_funct_2(D_57, u1_struct_0(A_43), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1(D_57, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_43), u1_struct_0('#skF_2')))) | ~v1_funct_2(D_57, u1_struct_0(A_43), u1_struct_0('#skF_2')) | ~v1_funct_1(D_57) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(A_43) | ~v2_pre_topc(A_43))), inference(superposition, [status(thm), theory('equality')], [c_4143, c_54])).
% 17.05/9.36  tff(c_5298, plain, (![D_381, A_382]: (v5_pre_topc(D_381, A_382, '#skF_2') | ~v5_pre_topc(D_381, A_382, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_subset_1(D_381, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_382), '#skF_4'))) | ~v1_funct_2(D_381, u1_struct_0(A_382), '#skF_4') | ~m1_subset_1(D_381, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_382), u1_struct_0('#skF_2')))) | ~v1_funct_2(D_381, u1_struct_0(A_382), u1_struct_0('#skF_2')) | ~v1_funct_1(D_381) | ~l1_pre_topc(A_382) | ~v2_pre_topc(A_382))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_4143, c_4183])).
% 17.05/9.36  tff(c_5308, plain, (![A_382]: (v5_pre_topc('#skF_4', A_382, '#skF_2') | ~v5_pre_topc('#skF_4', A_382, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_382), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_382), '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0(A_382), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(A_382) | ~v2_pre_topc(A_382) | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(A_382)))), inference(resolution, [status(thm)], [c_201, c_5298])).
% 17.05/9.36  tff(c_5316, plain, (![A_383]: (v5_pre_topc('#skF_4', A_383, '#skF_2') | ~v5_pre_topc('#skF_4', A_383, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_383), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_383), '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0(A_383), u1_struct_0('#skF_2')) | ~l1_pre_topc(A_383) | ~v2_pre_topc(A_383) | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(A_383)))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_5308])).
% 17.05/9.36  tff(c_5319, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_5231, c_5316])).
% 17.05/9.36  tff(c_5328, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_3860, c_78, c_76, c_3869, c_3860, c_4434, c_3860, c_5232, c_3860, c_5319])).
% 17.05/9.36  tff(c_5330, plain, $false, inference(negUnitSimplification, [status(thm)], [c_194, c_5328])).
% 17.05/9.36  tff(c_5331, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_433])).
% 17.05/9.36  tff(c_5362, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_5331, c_87])).
% 17.05/9.36  tff(c_5360, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_5331, c_91])).
% 17.05/9.36  tff(c_5435, plain, (k1_xboole_0='#skF_4' | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), k1_xboole_0) | u1_struct_0('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_5360, c_24])).
% 17.05/9.36  tff(c_5461, plain, (k1_xboole_0='#skF_4' | u1_struct_0('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_5362, c_5435])).
% 17.05/9.36  tff(c_5470, plain, (u1_struct_0('#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_5461])).
% 17.05/9.36  tff(c_5522, plain, (v4_relat_1('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_5470, c_144])).
% 17.05/9.36  tff(c_5524, plain, $false, inference(negUnitSimplification, [status(thm)], [c_375, c_5522])).
% 17.05/9.36  tff(c_5525, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_5461])).
% 17.05/9.36  tff(c_5533, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5525, c_5362])).
% 17.05/9.36  tff(c_5527, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_5525, c_5360])).
% 17.05/9.36  tff(c_5536, plain, (u1_struct_0('#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5525, c_5331])).
% 17.05/9.36  tff(c_5677, plain, (u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5536, c_5525, c_3858])).
% 17.05/9.36  tff(c_5333, plain, (![D_384, A_385, B_386]: (v5_pre_topc(D_384, A_385, B_386) | ~v5_pre_topc(D_384, A_385, g1_pre_topc(u1_struct_0(B_386), u1_pre_topc(B_386))) | ~m1_subset_1(D_384, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_385), u1_struct_0(g1_pre_topc(u1_struct_0(B_386), u1_pre_topc(B_386)))))) | ~v1_funct_2(D_384, u1_struct_0(A_385), u1_struct_0(g1_pre_topc(u1_struct_0(B_386), u1_pre_topc(B_386)))) | ~m1_subset_1(D_384, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_385), u1_struct_0(B_386)))) | ~v1_funct_2(D_384, u1_struct_0(A_385), u1_struct_0(B_386)) | ~v1_funct_1(D_384) | ~l1_pre_topc(B_386) | ~v2_pre_topc(B_386) | ~l1_pre_topc(A_385) | ~v2_pre_topc(A_385))), inference(cnfTransformation, [status(thm)], [f_163])).
% 17.05/9.36  tff(c_5337, plain, (![A_385]: (v5_pre_topc('#skF_4', A_385, '#skF_2') | ~v5_pre_topc('#skF_4', A_385, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_385), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_385), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0(A_385), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(A_385) | ~v2_pre_topc(A_385) | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(A_385)))), inference(resolution, [status(thm)], [c_200, c_5333])).
% 17.05/9.36  tff(c_5343, plain, (![A_385]: (v5_pre_topc('#skF_4', A_385, '#skF_2') | ~v5_pre_topc('#skF_4', A_385, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_385), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_385), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0(A_385), u1_struct_0('#skF_2')) | ~l1_pre_topc(A_385) | ~v2_pre_topc(A_385) | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(A_385)))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_64, c_5337])).
% 17.05/9.36  tff(c_6069, plain, (![A_416]: (v5_pre_topc('#skF_4', A_416, '#skF_2') | ~v5_pre_topc('#skF_4', A_416, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_416), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_416), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_416), '#skF_4') | ~l1_pre_topc(A_416) | ~v2_pre_topc(A_416) | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(A_416)))), inference(demodulation, [status(thm), theory('equality')], [c_5536, c_5536, c_5677, c_5536, c_5536, c_5343])).
% 17.05/9.36  tff(c_6078, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_5527, c_6069])).
% 17.05/9.36  tff(c_6091, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_5533, c_6078])).
% 17.05/9.36  tff(c_6092, plain, (~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_194, c_6091])).
% 17.05/9.36  tff(c_6097, plain, (~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_6092])).
% 17.05/9.36  tff(c_6100, plain, (~v4_relat_1('#skF_4', u1_struct_0('#skF_1')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_6097])).
% 17.05/9.36  tff(c_6104, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_110, c_144, c_6100])).
% 17.05/9.36  tff(c_6105, plain, (~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_6092])).
% 17.05/9.36  tff(c_5372, plain, (v2_pre_topc(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5331, c_46])).
% 17.05/9.36  tff(c_5389, plain, (v2_pre_topc(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_5372])).
% 17.05/9.36  tff(c_5530, plain, (v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_5525, c_5389])).
% 17.05/9.36  tff(c_5361, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_5331, c_62])).
% 17.05/9.36  tff(c_5534, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_5525, c_5361])).
% 17.05/9.36  tff(c_5784, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5677, c_5534])).
% 17.05/9.36  tff(c_5355, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_5331, c_162])).
% 17.05/9.36  tff(c_5862, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_5525, c_5355])).
% 17.05/9.36  tff(c_5378, plain, (l1_pre_topc(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5331, c_120])).
% 17.05/9.36  tff(c_5393, plain, (l1_pre_topc(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_5378])).
% 17.05/9.36  tff(c_5532, plain, (l1_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_5525, c_5393])).
% 17.05/9.36  tff(c_5358, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2'))))))), inference(demodulation, [status(thm), theory('equality')], [c_5331, c_60])).
% 17.05/9.36  tff(c_5611, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))))))), inference(demodulation, [status(thm), theory('equality')], [c_5525, c_5358])).
% 17.05/9.36  tff(c_5614, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_5611, c_50])).
% 17.05/9.36  tff(c_5634, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_5532, c_64, c_5614])).
% 17.05/9.36  tff(c_6319, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_5530, c_5533, c_5677, c_5527, c_5677, c_5784, c_5677, c_5862, c_5634])).
% 17.05/9.36  tff(c_6320, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6105, c_6319])).
% 17.05/9.36  tff(c_6322, plain, (r1_tarski(k1_relat_1('#skF_4'), k1_xboole_0)), inference(splitRight, [status(thm)], [c_227])).
% 17.05/9.36  tff(c_6414, plain, (![B_441, A_442, C_443]: (k1_xboole_0=B_441 | k1_relset_1(A_442, B_441, C_443)=A_442 | ~v1_funct_2(C_443, A_442, B_441) | ~m1_subset_1(C_443, k1_zfmisc_1(k2_zfmisc_1(A_442, B_441))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 17.05/9.36  tff(c_6426, plain, (u1_struct_0('#skF_2')=k1_xboole_0 | k1_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4')=u1_struct_0('#skF_1') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_91, c_6414])).
% 17.05/9.36  tff(c_6434, plain, (u1_struct_0('#skF_2')=k1_xboole_0 | u1_struct_0('#skF_1')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_87, c_173, c_6426])).
% 17.05/9.36  tff(c_6435, plain, (u1_struct_0('#skF_1')=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_6434])).
% 17.05/9.36  tff(c_6444, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_6435, c_87])).
% 17.05/9.36  tff(c_6442, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_6435, c_91])).
% 17.05/9.36  tff(c_6423, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0 | k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')=u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(resolution, [status(thm)], [c_60, c_6414])).
% 17.05/9.36  tff(c_6431, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0 | u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_172, c_6423])).
% 17.05/9.36  tff(c_6540, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0 | u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6435, c_6431])).
% 17.05/9.36  tff(c_6541, plain, (u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_6540])).
% 17.05/9.36  tff(c_6625, plain, (![D_447, A_448, B_449]: (v5_pre_topc(D_447, A_448, B_449) | ~v5_pre_topc(D_447, g1_pre_topc(u1_struct_0(A_448), u1_pre_topc(A_448)), B_449) | ~m1_subset_1(D_447, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_448), u1_pre_topc(A_448))), u1_struct_0(B_449)))) | ~v1_funct_2(D_447, u1_struct_0(g1_pre_topc(u1_struct_0(A_448), u1_pre_topc(A_448))), u1_struct_0(B_449)) | ~m1_subset_1(D_447, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_448), u1_struct_0(B_449)))) | ~v1_funct_2(D_447, u1_struct_0(A_448), u1_struct_0(B_449)) | ~v1_funct_1(D_447) | ~l1_pre_topc(B_449) | ~v2_pre_topc(B_449) | ~l1_pre_topc(A_448) | ~v2_pre_topc(A_448))), inference(cnfTransformation, [status(thm)], [f_134])).
% 17.05/9.36  tff(c_6634, plain, (![D_447, B_449]: (v5_pre_topc(D_447, '#skF_1', B_449) | ~v5_pre_topc(D_447, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_449) | ~m1_subset_1(D_447, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(B_449)))) | ~v1_funct_2(D_447, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_449)) | ~m1_subset_1(D_447, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_449)))) | ~v1_funct_2(D_447, u1_struct_0('#skF_1'), u1_struct_0(B_449)) | ~v1_funct_1(D_447) | ~l1_pre_topc(B_449) | ~v2_pre_topc(B_449) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_6435, c_6625])).
% 17.05/9.36  tff(c_9882, plain, (![D_642, B_643]: (v5_pre_topc(D_642, '#skF_1', B_643) | ~v5_pre_topc(D_642, g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), B_643) | ~m1_subset_1(D_642, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_643)))) | ~v1_funct_2(D_642, k1_relat_1('#skF_4'), u1_struct_0(B_643)) | ~v1_funct_1(D_642) | ~l1_pre_topc(B_643) | ~v2_pre_topc(B_643))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_6435, c_6435, c_6541, c_6435, c_6541, c_6435, c_6634])).
% 17.05/9.36  tff(c_9891, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), '#skF_2') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_6442, c_9882])).
% 17.05/9.36  tff(c_9910, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_64, c_6444, c_9891])).
% 17.05/9.36  tff(c_9911, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_194, c_9910])).
% 17.05/9.36  tff(c_6450, plain, (v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6435, c_46])).
% 17.05/9.36  tff(c_6463, plain, (v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_6450])).
% 17.05/9.36  tff(c_6456, plain, (l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6435, c_120])).
% 17.05/9.36  tff(c_6467, plain, (l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_6456])).
% 17.05/9.36  tff(c_6443, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_6435, c_62])).
% 17.05/9.36  tff(c_6589, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_6541, c_6443])).
% 17.05/9.36  tff(c_6437, plain, (v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_6435, c_162])).
% 17.05/9.36  tff(c_9941, plain, (![D_644, A_645, B_646]: (v5_pre_topc(D_644, A_645, B_646) | ~v5_pre_topc(D_644, A_645, g1_pre_topc(u1_struct_0(B_646), u1_pre_topc(B_646))) | ~m1_subset_1(D_644, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_645), u1_struct_0(g1_pre_topc(u1_struct_0(B_646), u1_pre_topc(B_646)))))) | ~v1_funct_2(D_644, u1_struct_0(A_645), u1_struct_0(g1_pre_topc(u1_struct_0(B_646), u1_pre_topc(B_646)))) | ~m1_subset_1(D_644, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_645), u1_struct_0(B_646)))) | ~v1_funct_2(D_644, u1_struct_0(A_645), u1_struct_0(B_646)) | ~v1_funct_1(D_644) | ~l1_pre_topc(B_646) | ~v2_pre_topc(B_646) | ~l1_pre_topc(A_645) | ~v2_pre_topc(A_645))), inference(cnfTransformation, [status(thm)], [f_163])).
% 17.05/9.36  tff(c_9957, plain, (![A_645]: (v5_pre_topc('#skF_4', A_645, '#skF_2') | ~v5_pre_topc('#skF_4', A_645, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_645), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_645), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0(A_645), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(A_645) | ~v2_pre_topc(A_645) | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(A_645)))), inference(resolution, [status(thm)], [c_200, c_9941])).
% 17.05/9.36  tff(c_10040, plain, (![A_656]: (v5_pre_topc('#skF_4', A_656, '#skF_2') | ~v5_pre_topc('#skF_4', A_656, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_656), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_656), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0(A_656), u1_struct_0('#skF_2')) | ~l1_pre_topc(A_656) | ~v2_pre_topc(A_656) | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(A_656)))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_64, c_9957])).
% 17.05/9.36  tff(c_10046, plain, (v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), '#skF_2') | ~v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0('#skF_2')) | ~l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))) | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_6541, c_10040])).
% 17.05/9.36  tff(c_10052, plain, (v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6541, c_6463, c_6467, c_6444, c_6541, c_6442, c_6541, c_6589, c_6437, c_10046])).
% 17.05/9.36  tff(c_10054, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9911, c_10052])).
% 17.05/9.36  tff(c_10055, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0), inference(splitRight, [status(thm)], [c_6540])).
% 17.05/9.36  tff(c_312, plain, (![B_117]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_117, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))))) | ~r1_tarski(k1_relat_1('#skF_4'), B_117))), inference(resolution, [status(thm)], [c_60, c_195])).
% 17.05/9.36  tff(c_26, plain, (![C_20, B_19]: (v1_funct_2(C_20, k1_xboole_0, B_19) | k1_relset_1(k1_xboole_0, B_19, C_20)!=k1_xboole_0 | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_19))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 17.05/9.36  tff(c_340, plain, (v1_funct_2('#skF_4', k1_xboole_0, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | k1_relset_1(k1_xboole_0, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')!=k1_xboole_0 | ~r1_tarski(k1_relat_1('#skF_4'), k1_xboole_0)), inference(resolution, [status(thm)], [c_312, c_26])).
% 17.05/9.36  tff(c_6386, plain, (v1_funct_2('#skF_4', k1_xboole_0, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | k1_relset_1(k1_xboole_0, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6322, c_340])).
% 17.05/9.36  tff(c_6387, plain, (k1_relset_1(k1_xboole_0, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_6386])).
% 17.05/9.36  tff(c_10058, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10055, c_6387])).
% 17.05/9.36  tff(c_10134, plain, (![B_657]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_657, k1_xboole_0))) | ~r1_tarski(k1_relat_1('#skF_4'), B_657))), inference(demodulation, [status(thm), theory('equality')], [c_10055, c_200])).
% 17.05/9.36  tff(c_10153, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_4', k1_xboole_0, k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_4'), k1_xboole_0)), inference(resolution, [status(thm)], [c_10134, c_30])).
% 17.05/9.36  tff(c_10182, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_4', k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6322, c_10153])).
% 17.05/9.36  tff(c_10183, plain, (~v1_funct_2('#skF_4', k1_xboole_0, k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_10058, c_10182])).
% 17.05/9.36  tff(c_6439, plain, (v4_relat_1('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_6435, c_143])).
% 17.05/9.36  tff(c_10057, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10055, c_6443])).
% 17.05/9.36  tff(c_10184, plain, (![B_657]: (k1_xboole_0='#skF_4' | ~v1_funct_2('#skF_4', B_657, k1_xboole_0) | k1_xboole_0=B_657 | ~r1_tarski(k1_relat_1('#skF_4'), B_657))), inference(resolution, [status(thm)], [c_10134, c_24])).
% 17.05/9.36  tff(c_10270, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_10184])).
% 17.05/9.36  tff(c_10312, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10270, c_10055])).
% 17.05/9.36  tff(c_10060, plain, (![B_107]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_107, k1_xboole_0))) | ~r1_tarski(k1_relat_1('#skF_4'), B_107))), inference(demodulation, [status(thm), theory('equality')], [c_10055, c_200])).
% 17.05/9.36  tff(c_10308, plain, (![B_107]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_107, '#skF_4'))) | ~r1_tarski(k1_relat_1('#skF_4'), B_107))), inference(demodulation, [status(thm), theory('equality')], [c_10270, c_10060])).
% 17.05/9.36  tff(c_18, plain, (![A_11, B_12, C_13]: (k1_relset_1(A_11, B_12, C_13)=k1_relat_1(C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 17.05/9.36  tff(c_342, plain, (![B_117]: (k1_relset_1(B_117, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')=k1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), B_117))), inference(resolution, [status(thm)], [c_312, c_18])).
% 17.05/9.36  tff(c_6390, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | ~r1_tarski(k1_relat_1('#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_342, c_6387])).
% 17.05/9.36  tff(c_6392, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6322, c_6390])).
% 17.05/9.36  tff(c_10314, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10270, c_6392])).
% 17.05/9.36  tff(c_10591, plain, (![A_672]: (v1_funct_2('#skF_4', A_672, '#skF_4') | A_672='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_672, '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_10270, c_10270, c_10270, c_10270, c_10270, c_22])).
% 17.05/9.36  tff(c_10602, plain, (![B_673]: (v1_funct_2('#skF_4', B_673, '#skF_4') | B_673='#skF_4' | ~r1_tarski(k1_relat_1('#skF_4'), B_673))), inference(resolution, [status(thm)], [c_10308, c_10591])).
% 17.05/9.36  tff(c_10613, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_4') | k1_relat_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_6, c_10602])).
% 17.05/9.36  tff(c_10623, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_10314, c_10613])).
% 17.05/9.36  tff(c_10208, plain, (![D_659, A_660, B_661]: (v5_pre_topc(D_659, A_660, B_661) | ~v5_pre_topc(D_659, A_660, g1_pre_topc(u1_struct_0(B_661), u1_pre_topc(B_661))) | ~m1_subset_1(D_659, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_660), u1_struct_0(g1_pre_topc(u1_struct_0(B_661), u1_pre_topc(B_661)))))) | ~v1_funct_2(D_659, u1_struct_0(A_660), u1_struct_0(g1_pre_topc(u1_struct_0(B_661), u1_pre_topc(B_661)))) | ~m1_subset_1(D_659, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_660), u1_struct_0(B_661)))) | ~v1_funct_2(D_659, u1_struct_0(A_660), u1_struct_0(B_661)) | ~v1_funct_1(D_659) | ~l1_pre_topc(B_661) | ~v2_pre_topc(B_661) | ~l1_pre_topc(A_660) | ~v2_pre_topc(A_660))), inference(cnfTransformation, [status(thm)], [f_163])).
% 17.05/9.36  tff(c_10217, plain, (![D_659, A_660]: (v5_pre_topc(D_659, A_660, '#skF_2') | ~v5_pre_topc(D_659, A_660, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_subset_1(D_659, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_660), k1_xboole_0))) | ~v1_funct_2(D_659, u1_struct_0(A_660), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1(D_659, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_660), u1_struct_0('#skF_2')))) | ~v1_funct_2(D_659, u1_struct_0(A_660), u1_struct_0('#skF_2')) | ~v1_funct_1(D_659) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(A_660) | ~v2_pre_topc(A_660))), inference(superposition, [status(thm), theory('equality')], [c_10055, c_10208])).
% 17.05/9.36  tff(c_10227, plain, (![D_659, A_660]: (v5_pre_topc(D_659, A_660, '#skF_2') | ~v5_pre_topc(D_659, A_660, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_subset_1(D_659, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_660), k1_xboole_0))) | ~v1_funct_2(D_659, u1_struct_0(A_660), k1_xboole_0) | ~m1_subset_1(D_659, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_660), u1_struct_0('#skF_2')))) | ~v1_funct_2(D_659, u1_struct_0(A_660), u1_struct_0('#skF_2')) | ~v1_funct_1(D_659) | ~l1_pre_topc(A_660) | ~v2_pre_topc(A_660))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_10055, c_10217])).
% 17.05/9.36  tff(c_11373, plain, (![D_718, A_719]: (v5_pre_topc(D_718, A_719, '#skF_2') | ~v5_pre_topc(D_718, A_719, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_subset_1(D_718, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_719), '#skF_4'))) | ~v1_funct_2(D_718, u1_struct_0(A_719), '#skF_4') | ~m1_subset_1(D_718, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_719), u1_struct_0('#skF_2')))) | ~v1_funct_2(D_718, u1_struct_0(A_719), u1_struct_0('#skF_2')) | ~v1_funct_1(D_718) | ~l1_pre_topc(A_719) | ~v2_pre_topc(A_719))), inference(demodulation, [status(thm), theory('equality')], [c_10270, c_10270, c_10227])).
% 17.05/9.36  tff(c_11379, plain, (![D_718]: (v5_pre_topc(D_718, '#skF_1', '#skF_2') | ~v5_pre_topc(D_718, '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_subset_1(D_718, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), '#skF_4'))) | ~v1_funct_2(D_718, u1_struct_0('#skF_1'), '#skF_4') | ~m1_subset_1(D_718, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(D_718, u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(D_718) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_6435, c_11373])).
% 17.05/9.36  tff(c_11489, plain, (![D_723]: (v5_pre_topc(D_723, '#skF_1', '#skF_2') | ~v5_pre_topc(D_723, '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_subset_1(D_723, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_4'))) | ~v1_funct_2(D_723, k1_relat_1('#skF_4'), '#skF_4') | ~m1_subset_1(D_723, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(D_723, k1_relat_1('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(D_723))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_6435, c_6435, c_6435, c_11379])).
% 17.05/9.36  tff(c_11492, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_4'))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_4') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_6442, c_11489])).
% 17.05/9.36  tff(c_11499, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_6444, c_10623, c_11492])).
% 17.05/9.36  tff(c_11500, plain, (~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_194, c_11499])).
% 17.05/9.36  tff(c_11505, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_4')))), inference(splitLeft, [status(thm)], [c_11500])).
% 17.05/9.36  tff(c_11508, plain, (~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_10308, c_11505])).
% 17.05/9.36  tff(c_11512, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_11508])).
% 17.05/9.36  tff(c_11513, plain, (~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_11500])).
% 17.05/9.36  tff(c_11514, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_4')))), inference(splitRight, [status(thm)], [c_11500])).
% 17.05/9.36  tff(c_10309, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10270, c_10057])).
% 17.05/9.36  tff(c_6441, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))))), inference(demodulation, [status(thm), theory('equality')], [c_6435, c_60])).
% 17.05/9.36  tff(c_10091, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10055, c_6441])).
% 17.05/9.36  tff(c_10310, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_10270, c_10091])).
% 17.05/9.36  tff(c_10080, plain, (l1_pre_topc(g1_pre_topc(k1_xboole_0, u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_10055, c_120])).
% 17.05/9.36  tff(c_11243, plain, (l1_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_10270, c_10080])).
% 17.05/9.36  tff(c_11244, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_11243])).
% 17.05/9.36  tff(c_11249, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_120, c_11244])).
% 17.05/9.36  tff(c_11253, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_11249])).
% 17.05/9.36  tff(c_11255, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_11243])).
% 17.05/9.36  tff(c_10074, plain, (v2_pre_topc(g1_pre_topc(k1_xboole_0, u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_10055, c_46])).
% 17.05/9.36  tff(c_11340, plain, (v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_11255, c_10270, c_10074])).
% 17.05/9.36  tff(c_11341, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_11340])).
% 17.05/9.36  tff(c_11344, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_46, c_11341])).
% 17.05/9.36  tff(c_11348, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_11344])).
% 17.05/9.36  tff(c_11350, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_11340])).
% 17.05/9.36  tff(c_28, plain, (![B_19, C_20, A_18]: (k1_xboole_0=B_19 | v1_funct_2(C_20, A_18, B_19) | k1_relset_1(A_18, B_19, C_20)!=A_18 | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 17.05/9.36  tff(c_338, plain, (![B_117]: (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0 | v1_funct_2('#skF_4', B_117, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | k1_relset_1(B_117, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')!=B_117 | ~r1_tarski(k1_relat_1('#skF_4'), B_117))), inference(resolution, [status(thm)], [c_312, c_28])).
% 17.05/9.36  tff(c_10379, plain, (![B_117]: (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))='#skF_4' | v1_funct_2('#skF_4', B_117, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | k1_relset_1(B_117, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')!=B_117 | ~r1_tarski(k1_relat_1('#skF_4'), B_117))), inference(demodulation, [status(thm), theory('equality')], [c_10270, c_338])).
% 17.05/9.36  tff(c_10380, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))='#skF_4'), inference(splitLeft, [status(thm)], [c_10379])).
% 17.05/9.36  tff(c_10361, plain, (![D_666, A_667, B_668]: (v5_pre_topc(D_666, A_667, B_668) | ~v5_pre_topc(D_666, g1_pre_topc(u1_struct_0(A_667), u1_pre_topc(A_667)), B_668) | ~m1_subset_1(D_666, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_667), u1_pre_topc(A_667))), u1_struct_0(B_668)))) | ~v1_funct_2(D_666, u1_struct_0(g1_pre_topc(u1_struct_0(A_667), u1_pre_topc(A_667))), u1_struct_0(B_668)) | ~m1_subset_1(D_666, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_667), u1_struct_0(B_668)))) | ~v1_funct_2(D_666, u1_struct_0(A_667), u1_struct_0(B_668)) | ~v1_funct_1(D_666) | ~l1_pre_topc(B_668) | ~v2_pre_topc(B_668) | ~l1_pre_topc(A_667) | ~v2_pre_topc(A_667))), inference(cnfTransformation, [status(thm)], [f_134])).
% 17.05/9.36  tff(c_10364, plain, (![D_666, B_668]: (v5_pre_topc(D_666, '#skF_1', B_668) | ~v5_pre_topc(D_666, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_668) | ~m1_subset_1(D_666, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(B_668)))) | ~v1_funct_2(D_666, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_668)) | ~m1_subset_1(D_666, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_668)))) | ~v1_funct_2(D_666, u1_struct_0('#skF_1'), u1_struct_0(B_668)) | ~v1_funct_1(D_666) | ~l1_pre_topc(B_668) | ~v2_pre_topc(B_668) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_6435, c_10361])).
% 17.05/9.36  tff(c_11767, plain, (![D_741, B_742]: (v5_pre_topc(D_741, '#skF_1', B_742) | ~v5_pre_topc(D_741, g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), B_742) | ~m1_subset_1(D_741, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(B_742)))) | ~v1_funct_2(D_741, u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(B_742)) | ~m1_subset_1(D_741, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_742)))) | ~v1_funct_2(D_741, k1_relat_1('#skF_4'), u1_struct_0(B_742)) | ~v1_funct_1(D_741) | ~l1_pre_topc(B_742) | ~v2_pre_topc(B_742))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_6435, c_6435, c_6435, c_6435, c_10364])).
% 17.05/9.36  tff(c_11770, plain, (![D_741]: (v5_pre_topc(D_741, '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc(D_741, g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_subset_1(D_741, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), '#skF_4'))) | ~v1_funct_2(D_741, u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1(D_741, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))))) | ~v1_funct_2(D_741, k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~v1_funct_1(D_741) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_10380, c_11767])).
% 17.05/9.36  tff(c_11930, plain, (![D_765]: (v5_pre_topc(D_765, '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc(D_765, g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_subset_1(D_765, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), '#skF_4'))) | ~v1_funct_2(D_765, u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), '#skF_4') | ~m1_subset_1(D_765, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_4'))) | ~v1_funct_2(D_765, k1_relat_1('#skF_4'), '#skF_4') | ~v1_funct_1(D_765))), inference(demodulation, [status(thm), theory('equality')], [c_11350, c_11255, c_10380, c_10380, c_10380, c_11770])).
% 17.05/9.36  tff(c_11940, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_4'))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_4') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_6437, c_11930])).
% 17.05/9.36  tff(c_11948, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_10623, c_11514, c_10309, c_10310, c_11940])).
% 17.05/9.36  tff(c_11950, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11513, c_11948])).
% 17.05/9.36  tff(c_11952, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))!='#skF_4'), inference(splitRight, [status(thm)], [c_10379])).
% 17.05/9.36  tff(c_12037, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10312, c_11952])).
% 17.05/9.36  tff(c_12040, plain, (![B_766]: (~v1_funct_2('#skF_4', B_766, k1_xboole_0) | k1_xboole_0=B_766 | ~r1_tarski(k1_relat_1('#skF_4'), B_766))), inference(splitRight, [status(thm)], [c_10184])).
% 17.05/9.36  tff(c_12047, plain, (![A_3]: (~v1_funct_2('#skF_4', A_3, k1_xboole_0) | k1_xboole_0=A_3 | ~v4_relat_1('#skF_4', A_3) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_10, c_12040])).
% 17.05/9.36  tff(c_12062, plain, (![A_767]: (~v1_funct_2('#skF_4', A_767, k1_xboole_0) | k1_xboole_0=A_767 | ~v4_relat_1('#skF_4', A_767))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_12047])).
% 17.05/9.36  tff(c_12065, plain, (u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))=k1_xboole_0 | ~v4_relat_1('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))))), inference(resolution, [status(thm)], [c_10057, c_12062])).
% 17.05/9.36  tff(c_12068, plain, (u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6439, c_12065])).
% 17.05/9.36  tff(c_12070, plain, (v1_funct_2('#skF_4', k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12068, c_10057])).
% 17.05/9.36  tff(c_12076, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10183, c_12070])).
% 17.05/9.36  tff(c_12077, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_6434])).
% 17.05/9.36  tff(c_228, plain, (![B_110]: (k1_relset_1(B_110, u1_struct_0('#skF_2'), '#skF_4')=k1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), B_110))), inference(resolution, [status(thm)], [c_202, c_18])).
% 17.05/9.36  tff(c_6334, plain, (k1_relset_1(k1_xboole_0, u1_struct_0('#skF_2'), '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_6322, c_228])).
% 17.05/9.36  tff(c_6321, plain, (~v1_funct_2('#skF_4', k1_xboole_0, u1_struct_0('#skF_2')) | k1_relset_1(k1_xboole_0, u1_struct_0('#skF_2'), '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_227])).
% 17.05/9.36  tff(c_6383, plain, (~v1_funct_2('#skF_4', k1_xboole_0, u1_struct_0('#skF_2')) | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6334, c_6321])).
% 17.05/9.36  tff(c_6384, plain, (~v1_funct_2('#skF_4', k1_xboole_0, u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_6383])).
% 17.05/9.36  tff(c_12081, plain, (~v1_funct_2('#skF_4', k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12077, c_6384])).
% 17.05/9.36  tff(c_12097, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12077, c_87])).
% 17.05/9.36  tff(c_12095, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12077, c_91])).
% 17.05/9.36  tff(c_12175, plain, (k1_xboole_0='#skF_4' | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), k1_xboole_0) | u1_struct_0('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_12095, c_24])).
% 17.05/9.36  tff(c_12201, plain, (k1_xboole_0='#skF_4' | u1_struct_0('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12097, c_12175])).
% 17.05/9.36  tff(c_12210, plain, (u1_struct_0('#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_12201])).
% 17.05/9.36  tff(c_12259, plain, (v1_funct_2('#skF_4', k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12210, c_12097])).
% 17.05/9.36  tff(c_12265, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12081, c_12259])).
% 17.05/9.36  tff(c_12266, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_12201])).
% 17.05/9.36  tff(c_12276, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12266, c_12097])).
% 17.05/9.36  tff(c_12268, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_12266, c_12095])).
% 17.05/9.36  tff(c_12281, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12266, c_6392])).
% 17.05/9.36  tff(c_12089, plain, (![B_107]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_107, k1_xboole_0))) | ~r1_tarski(k1_relat_1('#skF_4'), B_107))), inference(demodulation, [status(thm), theory('equality')], [c_12077, c_201])).
% 17.05/9.36  tff(c_12436, plain, (![B_107]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_107, '#skF_4'))) | ~r1_tarski(k1_relat_1('#skF_4'), B_107))), inference(demodulation, [status(thm), theory('equality')], [c_12266, c_12089])).
% 17.05/9.36  tff(c_12602, plain, (![A_784]: (v1_funct_2('#skF_4', A_784, '#skF_4') | A_784='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_784, '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_12266, c_12266, c_12266, c_12266, c_12266, c_22])).
% 17.05/9.36  tff(c_12613, plain, (![B_785]: (v1_funct_2('#skF_4', B_785, '#skF_4') | B_785='#skF_4' | ~r1_tarski(k1_relat_1('#skF_4'), B_785))), inference(resolution, [status(thm)], [c_12436, c_12602])).
% 17.05/9.36  tff(c_12624, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_4') | k1_relat_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_6, c_12613])).
% 17.05/9.36  tff(c_12634, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_12281, c_12624])).
% 17.05/9.36  tff(c_12279, plain, (u1_struct_0('#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12266, c_12077])).
% 17.05/9.36  tff(c_12665, plain, (u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))='#skF_4' | u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12279, c_12266, c_6431])).
% 17.05/9.36  tff(c_12666, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_12665])).
% 17.05/9.36  tff(c_12718, plain, (l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_12666, c_120])).
% 17.05/9.36  tff(c_12861, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_12718])).
% 17.05/9.36  tff(c_12864, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_120, c_12861])).
% 17.05/9.36  tff(c_12868, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_12864])).
% 17.05/9.36  tff(c_12870, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_12718])).
% 17.05/9.36  tff(c_12712, plain, (v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_12666, c_46])).
% 17.05/9.36  tff(c_13196, plain, (v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_12870, c_12712])).
% 17.05/9.36  tff(c_13197, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_13196])).
% 17.05/9.36  tff(c_13200, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_13197])).
% 17.05/9.36  tff(c_13204, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_13200])).
% 17.05/9.36  tff(c_13206, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_13196])).
% 17.05/9.36  tff(c_12096, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_12077, c_62])).
% 17.05/9.36  tff(c_12275, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_12266, c_12096])).
% 17.05/9.36  tff(c_12668, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_12666, c_12275])).
% 17.05/9.36  tff(c_12090, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_12077, c_162])).
% 17.05/9.36  tff(c_12553, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_12266, c_12090])).
% 17.05/9.36  tff(c_12085, plain, (![B_107]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_107, u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2')))))) | ~r1_tarski(k1_relat_1('#skF_4'), B_107))), inference(demodulation, [status(thm), theory('equality')], [c_12077, c_200])).
% 17.05/9.36  tff(c_12559, plain, (![B_107]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_107, u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))))) | ~r1_tarski(k1_relat_1('#skF_4'), B_107))), inference(demodulation, [status(thm), theory('equality')], [c_12266, c_12085])).
% 17.05/9.36  tff(c_12122, plain, (![D_768, A_769, B_770]: (v5_pre_topc(D_768, A_769, B_770) | ~v5_pre_topc(D_768, A_769, g1_pre_topc(u1_struct_0(B_770), u1_pre_topc(B_770))) | ~m1_subset_1(D_768, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_769), u1_struct_0(g1_pre_topc(u1_struct_0(B_770), u1_pre_topc(B_770)))))) | ~v1_funct_2(D_768, u1_struct_0(A_769), u1_struct_0(g1_pre_topc(u1_struct_0(B_770), u1_pre_topc(B_770)))) | ~m1_subset_1(D_768, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_769), u1_struct_0(B_770)))) | ~v1_funct_2(D_768, u1_struct_0(A_769), u1_struct_0(B_770)) | ~v1_funct_1(D_768) | ~l1_pre_topc(B_770) | ~v2_pre_topc(B_770) | ~l1_pre_topc(A_769) | ~v2_pre_topc(A_769))), inference(cnfTransformation, [status(thm)], [f_163])).
% 17.05/9.36  tff(c_12128, plain, (![D_768, A_769]: (v5_pre_topc(D_768, A_769, '#skF_2') | ~v5_pre_topc(D_768, A_769, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_subset_1(D_768, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_769), u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2')))))) | ~v1_funct_2(D_768, u1_struct_0(A_769), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1(D_768, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_769), u1_struct_0('#skF_2')))) | ~v1_funct_2(D_768, u1_struct_0(A_769), u1_struct_0('#skF_2')) | ~v1_funct_1(D_768) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(A_769) | ~v2_pre_topc(A_769))), inference(superposition, [status(thm), theory('equality')], [c_12077, c_12122])).
% 17.05/9.36  tff(c_12132, plain, (![D_768, A_769]: (v5_pre_topc(D_768, A_769, '#skF_2') | ~v5_pre_topc(D_768, A_769, g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2'))) | ~m1_subset_1(D_768, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_769), u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2')))))) | ~v1_funct_2(D_768, u1_struct_0(A_769), u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2')))) | ~m1_subset_1(D_768, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_769), k1_xboole_0))) | ~v1_funct_2(D_768, u1_struct_0(A_769), k1_xboole_0) | ~v1_funct_1(D_768) | ~l1_pre_topc(A_769) | ~v2_pre_topc(A_769))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_12077, c_12077, c_12077, c_12077, c_12128])).
% 17.05/9.36  tff(c_13273, plain, (![D_814, A_815]: (v5_pre_topc(D_814, A_815, '#skF_2') | ~v5_pre_topc(D_814, A_815, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~m1_subset_1(D_814, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_815), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))))) | ~v1_funct_2(D_814, u1_struct_0(A_815), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~m1_subset_1(D_814, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_815), '#skF_4'))) | ~v1_funct_2(D_814, u1_struct_0(A_815), '#skF_4') | ~v1_funct_1(D_814) | ~l1_pre_topc(A_815) | ~v2_pre_topc(A_815))), inference(demodulation, [status(thm), theory('equality')], [c_12266, c_12266, c_12266, c_12266, c_12266, c_12132])).
% 17.05/9.36  tff(c_13280, plain, (![A_815]: (v5_pre_topc('#skF_4', A_815, '#skF_2') | ~v5_pre_topc('#skF_4', A_815, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_815), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_815), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_815), '#skF_4') | ~v1_funct_1('#skF_4') | ~l1_pre_topc(A_815) | ~v2_pre_topc(A_815) | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(A_815)))), inference(resolution, [status(thm)], [c_12559, c_13273])).
% 17.05/9.36  tff(c_13306, plain, (![A_817]: (v5_pre_topc('#skF_4', A_817, '#skF_2') | ~v5_pre_topc('#skF_4', A_817, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_817), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_817), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_817), '#skF_4') | ~l1_pre_topc(A_817) | ~v2_pre_topc(A_817) | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(A_817)))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_13280])).
% 17.05/9.36  tff(c_13312, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_12666, c_13306])).
% 17.05/9.36  tff(c_13318, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_12666, c_13206, c_12870, c_12634, c_12666, c_12666, c_12668, c_12553, c_13312])).
% 17.05/9.36  tff(c_13321, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_4')))), inference(splitLeft, [status(thm)], [c_13318])).
% 17.05/9.36  tff(c_13324, plain, (~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_12436, c_13321])).
% 17.05/9.36  tff(c_13328, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_13324])).
% 17.05/9.36  tff(c_13330, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_4')))), inference(splitRight, [status(thm)], [c_13318])).
% 17.05/9.36  tff(c_13329, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')), inference(splitRight, [status(thm)], [c_13318])).
% 17.05/9.36  tff(c_12697, plain, (![D_42, B_36]: (v5_pre_topc(D_42, '#skF_1', B_36) | ~v5_pre_topc(D_42, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_36) | ~m1_subset_1(D_42, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_36)))) | ~v1_funct_2(D_42, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_36)) | ~m1_subset_1(D_42, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_36)))) | ~v1_funct_2(D_42, u1_struct_0('#skF_1'), u1_struct_0(B_36)) | ~v1_funct_1(D_42) | ~l1_pre_topc(B_36) | ~v2_pre_topc(B_36) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_12666, c_50])).
% 17.05/9.36  tff(c_13212, plain, (![D_812, B_813]: (v5_pre_topc(D_812, '#skF_1', B_813) | ~v5_pre_topc(D_812, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_813) | ~m1_subset_1(D_812, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_813)))) | ~v1_funct_2(D_812, k1_relat_1('#skF_4'), u1_struct_0(B_813)) | ~m1_subset_1(D_812, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_813)))) | ~v1_funct_2(D_812, u1_struct_0('#skF_1'), u1_struct_0(B_813)) | ~v1_funct_1(D_812) | ~l1_pre_topc(B_813) | ~v2_pre_topc(B_813))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_12666, c_12697])).
% 17.05/9.36  tff(c_13222, plain, (![D_812]: (v5_pre_topc(D_812, '#skF_1', '#skF_2') | ~v5_pre_topc(D_812, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~m1_subset_1(D_812, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(D_812, k1_relat_1('#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(D_812, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), '#skF_4'))) | ~v1_funct_2(D_812, u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(D_812) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_12279, c_13212])).
% 17.05/9.36  tff(c_13229, plain, (![D_812]: (v5_pre_topc(D_812, '#skF_1', '#skF_2') | ~v5_pre_topc(D_812, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~m1_subset_1(D_812, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_4'))) | ~v1_funct_2(D_812, k1_relat_1('#skF_4'), '#skF_4') | ~m1_subset_1(D_812, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), '#skF_4'))) | ~v1_funct_2(D_812, u1_struct_0('#skF_1'), '#skF_4') | ~v1_funct_1(D_812))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_12279, c_12279, c_12279, c_13222])).
% 17.05/9.36  tff(c_13409, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_4'))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_13329, c_13229])).
% 17.05/9.36  tff(c_13412, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_12276, c_12268, c_12634, c_13330, c_13409])).
% 17.05/9.36  tff(c_13414, plain, $false, inference(negUnitSimplification, [status(thm)], [c_194, c_13412])).
% 17.05/9.36  tff(c_13415, plain, (u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))='#skF_4'), inference(splitRight, [status(thm)], [c_12665])).
% 17.05/9.36  tff(c_13419, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13415, c_12275])).
% 17.05/9.36  tff(c_12093, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2'))))))), inference(demodulation, [status(thm), theory('equality')], [c_12077, c_60])).
% 17.05/9.36  tff(c_12366, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))))))), inference(demodulation, [status(thm), theory('equality')], [c_12266, c_12093])).
% 17.05/9.36  tff(c_13421, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_13415, c_12366])).
% 17.05/9.36  tff(c_13630, plain, (![D_833, A_834]: (v5_pre_topc(D_833, A_834, '#skF_2') | ~v5_pre_topc(D_833, A_834, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~m1_subset_1(D_833, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_834), '#skF_4'))) | ~v1_funct_2(D_833, u1_struct_0(A_834), '#skF_4') | ~m1_subset_1(D_833, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_834), '#skF_4'))) | ~v1_funct_2(D_833, u1_struct_0(A_834), '#skF_4') | ~v1_funct_1(D_833) | ~l1_pre_topc(A_834) | ~v2_pre_topc(A_834))), inference(demodulation, [status(thm), theory('equality')], [c_12266, c_12266, c_13415, c_12266, c_13415, c_12266, c_12266, c_12132])).
% 17.05/9.36  tff(c_13632, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4') | ~v1_funct_1('#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_13421, c_13630])).
% 17.05/9.36  tff(c_13644, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_13419, c_13421, c_12553, c_13632])).
% 17.05/9.36  tff(c_13656, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_13644])).
% 17.05/9.36  tff(c_13659, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_13656])).
% 17.05/9.36  tff(c_13663, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_13659])).
% 17.05/9.36  tff(c_13664, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')), inference(splitRight, [status(thm)], [c_13644])).
% 17.05/9.36  tff(c_13667, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_13664])).
% 17.05/9.36  tff(c_13670, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_120, c_13667])).
% 17.05/9.36  tff(c_13674, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_13670])).
% 17.05/9.36  tff(c_13675, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')), inference(splitRight, [status(thm)], [c_13664])).
% 17.05/9.36  tff(c_12147, plain, (![D_771, A_772, B_773]: (v5_pre_topc(D_771, A_772, B_773) | ~v5_pre_topc(D_771, g1_pre_topc(u1_struct_0(A_772), u1_pre_topc(A_772)), B_773) | ~m1_subset_1(D_771, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_772), u1_pre_topc(A_772))), u1_struct_0(B_773)))) | ~v1_funct_2(D_771, u1_struct_0(g1_pre_topc(u1_struct_0(A_772), u1_pre_topc(A_772))), u1_struct_0(B_773)) | ~m1_subset_1(D_771, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_772), u1_struct_0(B_773)))) | ~v1_funct_2(D_771, u1_struct_0(A_772), u1_struct_0(B_773)) | ~v1_funct_1(D_771) | ~l1_pre_topc(B_773) | ~v2_pre_topc(B_773) | ~l1_pre_topc(A_772) | ~v2_pre_topc(A_772))), inference(cnfTransformation, [status(thm)], [f_134])).
% 17.05/9.36  tff(c_12153, plain, (![D_771, A_772]: (v5_pre_topc(D_771, A_772, '#skF_2') | ~v5_pre_topc(D_771, g1_pre_topc(u1_struct_0(A_772), u1_pre_topc(A_772)), '#skF_2') | ~m1_subset_1(D_771, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_772), u1_pre_topc(A_772))), k1_xboole_0))) | ~v1_funct_2(D_771, u1_struct_0(g1_pre_topc(u1_struct_0(A_772), u1_pre_topc(A_772))), u1_struct_0('#skF_2')) | ~m1_subset_1(D_771, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_772), u1_struct_0('#skF_2')))) | ~v1_funct_2(D_771, u1_struct_0(A_772), u1_struct_0('#skF_2')) | ~v1_funct_1(D_771) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(A_772) | ~v2_pre_topc(A_772))), inference(superposition, [status(thm), theory('equality')], [c_12077, c_12147])).
% 17.05/9.36  tff(c_12157, plain, (![D_771, A_772]: (v5_pre_topc(D_771, A_772, '#skF_2') | ~v5_pre_topc(D_771, g1_pre_topc(u1_struct_0(A_772), u1_pre_topc(A_772)), '#skF_2') | ~m1_subset_1(D_771, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_772), u1_pre_topc(A_772))), k1_xboole_0))) | ~v1_funct_2(D_771, u1_struct_0(g1_pre_topc(u1_struct_0(A_772), u1_pre_topc(A_772))), k1_xboole_0) | ~m1_subset_1(D_771, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_772), k1_xboole_0))) | ~v1_funct_2(D_771, u1_struct_0(A_772), k1_xboole_0) | ~v1_funct_1(D_771) | ~l1_pre_topc(A_772) | ~v2_pre_topc(A_772))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_12077, c_12077, c_12077, c_12153])).
% 17.05/9.36  tff(c_13757, plain, (![D_845, A_846]: (v5_pre_topc(D_845, A_846, '#skF_2') | ~v5_pre_topc(D_845, g1_pre_topc(u1_struct_0(A_846), u1_pre_topc(A_846)), '#skF_2') | ~m1_subset_1(D_845, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_846), u1_pre_topc(A_846))), '#skF_4'))) | ~v1_funct_2(D_845, u1_struct_0(g1_pre_topc(u1_struct_0(A_846), u1_pre_topc(A_846))), '#skF_4') | ~m1_subset_1(D_845, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_846), '#skF_4'))) | ~v1_funct_2(D_845, u1_struct_0(A_846), '#skF_4') | ~v1_funct_1(D_845) | ~l1_pre_topc(A_846) | ~v2_pre_topc(A_846))), inference(demodulation, [status(thm), theory('equality')], [c_12266, c_12266, c_12266, c_12266, c_12157])).
% 17.05/9.36  tff(c_13760, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4') | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_13421, c_13757])).
% 17.05/9.36  tff(c_13773, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_64, c_12276, c_12268, c_13419, c_13675, c_13760])).
% 17.05/9.36  tff(c_13775, plain, $false, inference(negUnitSimplification, [status(thm)], [c_194, c_13773])).
% 17.05/9.36  tff(c_13777, plain, (k1_relset_1(k1_xboole_0, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_6386])).
% 17.05/9.36  tff(c_13781, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | ~r1_tarski(k1_relat_1('#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_13777, c_342])).
% 17.05/9.36  tff(c_13788, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6322, c_13781])).
% 17.05/9.36  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 17.05/9.36  tff(c_6339, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_6322, c_2])).
% 17.05/9.36  tff(c_6341, plain, (~r1_tarski(k1_xboole_0, k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_6339])).
% 17.05/9.36  tff(c_13793, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_13788, c_6341])).
% 17.05/9.36  tff(c_13807, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_13793])).
% 17.05/9.36  tff(c_13808, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_6383])).
% 17.05/9.36  tff(c_13814, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_13808, c_6341])).
% 17.05/9.36  tff(c_13828, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_13814])).
% 17.05/9.36  tff(c_13829, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_6339])).
% 17.05/9.36  tff(c_13841, plain, (k1_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_13829, c_173])).
% 17.05/9.36  tff(c_13951, plain, (![B_853, A_854, C_855]: (k1_xboole_0=B_853 | k1_relset_1(A_854, B_853, C_855)=A_854 | ~v1_funct_2(C_855, A_854, B_853) | ~m1_subset_1(C_855, k1_zfmisc_1(k2_zfmisc_1(A_854, B_853))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 17.05/9.36  tff(c_13957, plain, (u1_struct_0('#skF_2')=k1_xboole_0 | k1_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4')=u1_struct_0('#skF_1') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_91, c_13951])).
% 17.05/9.36  tff(c_13963, plain, (u1_struct_0('#skF_2')=k1_xboole_0 | u1_struct_0('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_87, c_13841, c_13957])).
% 17.05/9.36  tff(c_13964, plain, (u1_struct_0('#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_13963])).
% 17.05/9.36  tff(c_13856, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3) | ~v4_relat_1('#skF_4', A_3) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_13829, c_10])).
% 17.05/9.36  tff(c_13887, plain, (![A_851]: (r1_tarski(k1_xboole_0, A_851) | ~v4_relat_1('#skF_4', A_851))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_13856])).
% 17.05/9.36  tff(c_13911, plain, (r1_tarski(k1_xboole_0, u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_144, c_13887])).
% 17.05/9.36  tff(c_13914, plain, (u1_struct_0('#skF_1')=k1_xboole_0 | ~r1_tarski(u1_struct_0('#skF_1'), k1_xboole_0)), inference(resolution, [status(thm)], [c_13911, c_2])).
% 17.05/9.36  tff(c_13923, plain, (~r1_tarski(u1_struct_0('#skF_1'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_13914])).
% 17.05/9.36  tff(c_13965, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_13964, c_13923])).
% 17.05/9.36  tff(c_13978, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_13965])).
% 17.05/9.36  tff(c_13980, plain, (u1_struct_0('#skF_1')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_13963])).
% 17.05/9.36  tff(c_13979, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_13963])).
% 17.05/9.36  tff(c_14042, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_13979, c_87])).
% 17.05/9.36  tff(c_14040, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_13979, c_91])).
% 17.05/9.36  tff(c_14109, plain, (k1_xboole_0='#skF_4' | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), k1_xboole_0) | u1_struct_0('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_14040, c_24])).
% 17.05/9.36  tff(c_14136, plain, (k1_xboole_0='#skF_4' | u1_struct_0('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_14042, c_14109])).
% 17.05/9.36  tff(c_14137, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_13980, c_14136])).
% 17.05/9.36  tff(c_14154, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14137, c_14042])).
% 17.05/9.36  tff(c_14146, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_14137, c_14040])).
% 17.05/9.36  tff(c_14046, plain, (v2_pre_topc(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_13979, c_46])).
% 17.05/9.36  tff(c_14059, plain, (v2_pre_topc(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_14046])).
% 17.05/9.36  tff(c_14153, plain, (v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_14137, c_14059])).
% 17.05/9.36  tff(c_14052, plain, (l1_pre_topc(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_13979, c_120])).
% 17.05/9.36  tff(c_14063, plain, (l1_pre_topc(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_14052])).
% 17.05/9.36  tff(c_14151, plain, (l1_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_14137, c_14063])).
% 17.05/9.36  tff(c_14041, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_13979, c_62])).
% 17.05/9.36  tff(c_14149, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_14137, c_14041])).
% 17.05/9.36  tff(c_14157, plain, (u1_struct_0('#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_14137, c_13979])).
% 17.05/9.36  tff(c_13833, plain, (k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_13829, c_172])).
% 17.05/9.36  tff(c_14428, plain, (k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_14157, c_14137, c_13833])).
% 17.05/9.36  tff(c_14038, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2'))))))), inference(demodulation, [status(thm), theory('equality')], [c_13979, c_60])).
% 17.05/9.36  tff(c_14246, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))))))), inference(demodulation, [status(thm), theory('equality')], [c_14137, c_14038])).
% 17.05/9.36  tff(c_32, plain, (![B_19, A_18, C_20]: (k1_xboole_0=B_19 | k1_relset_1(A_18, B_19, C_20)=A_18 | ~v1_funct_2(C_20, A_18, B_19) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 17.05/9.36  tff(c_14727, plain, (![B_892, A_893, C_894]: (B_892='#skF_4' | k1_relset_1(A_893, B_892, C_894)=A_893 | ~v1_funct_2(C_894, A_893, B_892) | ~m1_subset_1(C_894, k1_zfmisc_1(k2_zfmisc_1(A_893, B_892))))), inference(demodulation, [status(thm), theory('equality')], [c_14137, c_32])).
% 17.05/9.36  tff(c_14739, plain, (u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))='#skF_4' | k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))), '#skF_4')=u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))))), inference(resolution, [status(thm)], [c_14246, c_14727])).
% 17.05/9.36  tff(c_14750, plain, (u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))='#skF_4' | u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_14149, c_14428, c_14739])).
% 17.05/9.36  tff(c_14752, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))='#skF_4'), inference(splitLeft, [status(thm)], [c_14750])).
% 17.05/9.36  tff(c_112, plain, (![B_77, A_78]: (r1_tarski(k1_relat_1(B_77), A_78) | ~v4_relat_1(B_77, A_78) | ~v1_relat_1(B_77))), inference(cnfTransformation, [status(thm)], [f_37])).
% 17.05/9.36  tff(c_115, plain, (![B_77, A_78]: (k1_relat_1(B_77)=A_78 | ~r1_tarski(A_78, k1_relat_1(B_77)) | ~v4_relat_1(B_77, A_78) | ~v1_relat_1(B_77))), inference(resolution, [status(thm)], [c_112, c_2])).
% 17.05/9.36  tff(c_13847, plain, (![A_78]: (k1_relat_1('#skF_4')=A_78 | ~r1_tarski(A_78, k1_xboole_0) | ~v4_relat_1('#skF_4', A_78) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_13829, c_115])).
% 17.05/9.36  tff(c_13924, plain, (![A_852]: (k1_xboole_0=A_852 | ~r1_tarski(A_852, k1_xboole_0) | ~v4_relat_1('#skF_4', A_852))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_13829, c_13847])).
% 17.05/9.36  tff(c_13949, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=k1_xboole_0 | ~r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), k1_xboole_0)), inference(resolution, [status(thm)], [c_143, c_13924])).
% 17.05/9.36  tff(c_14516, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))='#skF_4' | ~r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14137, c_14137, c_13949])).
% 17.05/9.36  tff(c_14517, plain, (~r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4')), inference(splitLeft, [status(thm)], [c_14516])).
% 17.05/9.36  tff(c_14753, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14752, c_14517])).
% 17.05/9.36  tff(c_14762, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_14753])).
% 17.05/9.36  tff(c_14764, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))!='#skF_4'), inference(splitRight, [status(thm)], [c_14750])).
% 17.05/9.36  tff(c_247, plain, (![B_112]: (k1_relset_1(B_112, u1_struct_0('#skF_2'), '#skF_4')=k1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), B_112))), inference(resolution, [status(thm)], [c_202, c_18])).
% 17.05/9.36  tff(c_251, plain, (![A_3]: (k1_relset_1(A_3, u1_struct_0('#skF_2'), '#skF_4')=k1_relat_1('#skF_4') | ~v4_relat_1('#skF_4', A_3) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_10, c_247])).
% 17.05/9.36  tff(c_258, plain, (![A_3]: (k1_relset_1(A_3, u1_struct_0('#skF_2'), '#skF_4')=k1_relat_1('#skF_4') | ~v4_relat_1('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_251])).
% 17.05/9.36  tff(c_13835, plain, (![A_3]: (k1_relset_1(A_3, u1_struct_0('#skF_2'), '#skF_4')=k1_xboole_0 | ~v4_relat_1('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_13829, c_258])).
% 17.05/9.36  tff(c_14452, plain, (![A_873]: (k1_relset_1(A_873, '#skF_4', '#skF_4')='#skF_4' | ~v4_relat_1('#skF_4', A_873))), inference(demodulation, [status(thm), theory('equality')], [c_14157, c_14137, c_13835])).
% 17.05/9.36  tff(c_14475, plain, (k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_143, c_14452])).
% 17.05/9.36  tff(c_14763, plain, (u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))='#skF_4'), inference(splitRight, [status(thm)], [c_14750])).
% 17.05/9.36  tff(c_13954, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0 | k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')=u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(resolution, [status(thm)], [c_60, c_13951])).
% 17.05/9.36  tff(c_13960, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0 | k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')=u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_13954])).
% 17.05/9.36  tff(c_14397, plain, (u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))='#skF_4' | k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))), '#skF_4')=u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_14157, c_14157, c_14137, c_13960])).
% 17.05/9.36  tff(c_14398, plain, (k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))), '#skF_4')=u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_14397])).
% 17.05/9.36  tff(c_14916, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_14475, c_14763, c_14398])).
% 17.05/9.36  tff(c_14917, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14764, c_14916])).
% 17.05/9.36  tff(c_14918, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))='#skF_4'), inference(splitRight, [status(thm)], [c_14516])).
% 17.05/9.36  tff(c_14166, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_14137, c_13829])).
% 17.05/9.36  tff(c_259, plain, (k1_relset_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'), '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_6, c_247])).
% 17.05/9.36  tff(c_13836, plain, (k1_relset_1(k1_xboole_0, u1_struct_0('#skF_2'), '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_13829, c_13829, c_259])).
% 17.05/9.36  tff(c_14035, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_13979, c_13836])).
% 17.05/9.36  tff(c_14155, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_14137, c_14137, c_14137, c_14035])).
% 17.05/9.36  tff(c_226, plain, (v1_funct_2('#skF_4', k1_xboole_0, u1_struct_0('#skF_2')) | k1_relset_1(k1_xboole_0, u1_struct_0('#skF_2'), '#skF_4')!=k1_xboole_0 | ~r1_tarski(k1_relat_1('#skF_4'), k1_xboole_0)), inference(resolution, [status(thm)], [c_202, c_26])).
% 17.05/9.36  tff(c_14999, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_14137, c_14166, c_14137, c_14155, c_14137, c_14157, c_14137, c_14157, c_226])).
% 17.05/9.36  tff(c_20, plain, (![D_17, B_15, C_16, A_14]: (m1_subset_1(D_17, k1_zfmisc_1(k2_zfmisc_1(B_15, C_16))) | ~r1_tarski(k1_relat_1(D_17), B_15) | ~m1_subset_1(D_17, k1_zfmisc_1(k2_zfmisc_1(A_14, C_16))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 17.05/9.36  tff(c_14106, plain, (![B_15]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_15, k1_xboole_0))) | ~r1_tarski(k1_relat_1('#skF_4'), B_15))), inference(resolution, [status(thm)], [c_14040, c_20])).
% 17.05/9.36  tff(c_14133, plain, (![B_15]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_15, k1_xboole_0))) | ~r1_tarski(k1_xboole_0, B_15))), inference(demodulation, [status(thm), theory('equality')], [c_13829, c_14106])).
% 17.05/9.36  tff(c_14478, plain, (![B_15]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_15, '#skF_4'))) | ~r1_tarski('#skF_4', B_15))), inference(demodulation, [status(thm), theory('equality')], [c_14137, c_14137, c_14133])).
% 17.05/9.36  tff(c_14071, plain, (![D_857, A_858, B_859]: (v5_pre_topc(D_857, A_858, B_859) | ~v5_pre_topc(D_857, g1_pre_topc(u1_struct_0(A_858), u1_pre_topc(A_858)), B_859) | ~m1_subset_1(D_857, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_858), u1_pre_topc(A_858))), u1_struct_0(B_859)))) | ~v1_funct_2(D_857, u1_struct_0(g1_pre_topc(u1_struct_0(A_858), u1_pre_topc(A_858))), u1_struct_0(B_859)) | ~m1_subset_1(D_857, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_858), u1_struct_0(B_859)))) | ~v1_funct_2(D_857, u1_struct_0(A_858), u1_struct_0(B_859)) | ~v1_funct_1(D_857) | ~l1_pre_topc(B_859) | ~v2_pre_topc(B_859) | ~l1_pre_topc(A_858) | ~v2_pre_topc(A_858))), inference(cnfTransformation, [status(thm)], [f_134])).
% 17.05/9.36  tff(c_14077, plain, (![D_857, A_858]: (v5_pre_topc(D_857, A_858, '#skF_2') | ~v5_pre_topc(D_857, g1_pre_topc(u1_struct_0(A_858), u1_pre_topc(A_858)), '#skF_2') | ~m1_subset_1(D_857, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_858), u1_pre_topc(A_858))), k1_xboole_0))) | ~v1_funct_2(D_857, u1_struct_0(g1_pre_topc(u1_struct_0(A_858), u1_pre_topc(A_858))), u1_struct_0('#skF_2')) | ~m1_subset_1(D_857, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_858), u1_struct_0('#skF_2')))) | ~v1_funct_2(D_857, u1_struct_0(A_858), u1_struct_0('#skF_2')) | ~v1_funct_1(D_857) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(A_858) | ~v2_pre_topc(A_858))), inference(superposition, [status(thm), theory('equality')], [c_13979, c_14071])).
% 17.05/9.36  tff(c_14081, plain, (![D_857, A_858]: (v5_pre_topc(D_857, A_858, '#skF_2') | ~v5_pre_topc(D_857, g1_pre_topc(u1_struct_0(A_858), u1_pre_topc(A_858)), '#skF_2') | ~m1_subset_1(D_857, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_858), u1_pre_topc(A_858))), k1_xboole_0))) | ~v1_funct_2(D_857, u1_struct_0(g1_pre_topc(u1_struct_0(A_858), u1_pre_topc(A_858))), k1_xboole_0) | ~m1_subset_1(D_857, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_858), k1_xboole_0))) | ~v1_funct_2(D_857, u1_struct_0(A_858), k1_xboole_0) | ~v1_funct_1(D_857) | ~l1_pre_topc(A_858) | ~v2_pre_topc(A_858))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_13979, c_13979, c_13979, c_14077])).
% 17.05/9.36  tff(c_16036, plain, (![D_983, A_984]: (v5_pre_topc(D_983, A_984, '#skF_2') | ~v5_pre_topc(D_983, g1_pre_topc(u1_struct_0(A_984), u1_pre_topc(A_984)), '#skF_2') | ~m1_subset_1(D_983, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_984), u1_pre_topc(A_984))), '#skF_4'))) | ~v1_funct_2(D_983, u1_struct_0(g1_pre_topc(u1_struct_0(A_984), u1_pre_topc(A_984))), '#skF_4') | ~m1_subset_1(D_983, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_984), '#skF_4'))) | ~v1_funct_2(D_983, u1_struct_0(A_984), '#skF_4') | ~v1_funct_1(D_983) | ~l1_pre_topc(A_984) | ~v2_pre_topc(A_984))), inference(demodulation, [status(thm), theory('equality')], [c_14137, c_14137, c_14137, c_14137, c_14081])).
% 17.05/9.36  tff(c_16046, plain, (![A_984]: (v5_pre_topc('#skF_4', A_984, '#skF_2') | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_984), u1_pre_topc(A_984)), '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_984), u1_pre_topc(A_984))), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_984), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_984), '#skF_4') | ~v1_funct_1('#skF_4') | ~l1_pre_topc(A_984) | ~v2_pre_topc(A_984) | ~r1_tarski('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_984), u1_pre_topc(A_984)))))), inference(resolution, [status(thm)], [c_14478, c_16036])).
% 17.05/9.36  tff(c_16079, plain, (![A_989]: (v5_pre_topc('#skF_4', A_989, '#skF_2') | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_989), u1_pre_topc(A_989)), '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_989), u1_pre_topc(A_989))), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_989), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_989), '#skF_4') | ~l1_pre_topc(A_989) | ~v2_pre_topc(A_989) | ~r1_tarski('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_989), u1_pre_topc(A_989)))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_16046])).
% 17.05/9.36  tff(c_16091, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~v1_funct_2('#skF_4', '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_14918, c_16079])).
% 17.05/9.36  tff(c_16100, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_14918, c_78, c_76, c_14154, c_14146, c_14999, c_16091])).
% 17.05/9.36  tff(c_16101, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_194, c_16100])).
% 17.05/9.36  tff(c_14974, plain, (l1_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_14918, c_120])).
% 17.05/9.36  tff(c_15214, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_14974])).
% 17.05/9.36  tff(c_15219, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_120, c_15214])).
% 17.05/9.36  tff(c_15223, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_15219])).
% 17.05/9.36  tff(c_15225, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_14974])).
% 17.05/9.36  tff(c_14968, plain, (v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_14918, c_46])).
% 17.05/9.36  tff(c_15889, plain, (v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_15225, c_14968])).
% 17.05/9.36  tff(c_15890, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_15889])).
% 17.05/9.36  tff(c_15893, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_15890])).
% 17.05/9.36  tff(c_15897, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_15893])).
% 17.05/9.36  tff(c_15899, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_15889])).
% 17.05/9.36  tff(c_14923, plain, (v1_funct_2('#skF_4', '#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_14918, c_14149])).
% 17.05/9.36  tff(c_13834, plain, (![B_107]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_107, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))))) | ~r1_tarski(k1_xboole_0, B_107))), inference(demodulation, [status(thm), theory('equality')], [c_13829, c_200])).
% 17.05/9.36  tff(c_14033, plain, (![B_107]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_107, u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2')))))) | ~r1_tarski(k1_xboole_0, B_107))), inference(demodulation, [status(thm), theory('equality')], [c_13979, c_13834])).
% 17.05/9.36  tff(c_15072, plain, (![B_107]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_107, u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))))) | ~r1_tarski('#skF_4', B_107))), inference(demodulation, [status(thm), theory('equality')], [c_14137, c_14137, c_14033])).
% 17.05/9.36  tff(c_14312, plain, (![D_867, A_868, B_869]: (v5_pre_topc(D_867, A_868, g1_pre_topc(u1_struct_0(B_869), u1_pre_topc(B_869))) | ~v5_pre_topc(D_867, A_868, B_869) | ~m1_subset_1(D_867, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_868), u1_struct_0(g1_pre_topc(u1_struct_0(B_869), u1_pre_topc(B_869)))))) | ~v1_funct_2(D_867, u1_struct_0(A_868), u1_struct_0(g1_pre_topc(u1_struct_0(B_869), u1_pre_topc(B_869)))) | ~m1_subset_1(D_867, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_868), u1_struct_0(B_869)))) | ~v1_funct_2(D_867, u1_struct_0(A_868), u1_struct_0(B_869)) | ~v1_funct_1(D_867) | ~l1_pre_topc(B_869) | ~v2_pre_topc(B_869) | ~l1_pre_topc(A_868) | ~v2_pre_topc(A_868))), inference(cnfTransformation, [status(thm)], [f_163])).
% 17.05/9.36  tff(c_14318, plain, (![D_867, A_868]: (v5_pre_topc(D_867, A_868, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc(D_867, A_868, '#skF_2') | ~m1_subset_1(D_867, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_868), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))))) | ~v1_funct_2(D_867, u1_struct_0(A_868), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1(D_867, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_868), u1_struct_0('#skF_2')))) | ~v1_funct_2(D_867, u1_struct_0(A_868), u1_struct_0('#skF_2')) | ~v1_funct_1(D_867) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(A_868) | ~v2_pre_topc(A_868))), inference(superposition, [status(thm), theory('equality')], [c_14157, c_14312])).
% 17.05/9.36  tff(c_16130, plain, (![D_991, A_992]: (v5_pre_topc(D_991, A_992, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc(D_991, A_992, '#skF_2') | ~m1_subset_1(D_991, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_992), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))))) | ~v1_funct_2(D_991, u1_struct_0(A_992), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~m1_subset_1(D_991, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_992), '#skF_4'))) | ~v1_funct_2(D_991, u1_struct_0(A_992), '#skF_4') | ~v1_funct_1(D_991) | ~l1_pre_topc(A_992) | ~v2_pre_topc(A_992))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_14157, c_14157, c_14157, c_14157, c_14318])).
% 17.05/9.36  tff(c_16134, plain, (![A_992]: (v5_pre_topc('#skF_4', A_992, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', A_992, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0(A_992), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_992), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_992), '#skF_4') | ~v1_funct_1('#skF_4') | ~l1_pre_topc(A_992) | ~v2_pre_topc(A_992) | ~r1_tarski('#skF_4', u1_struct_0(A_992)))), inference(resolution, [status(thm)], [c_15072, c_16130])).
% 17.05/9.36  tff(c_16148, plain, (![A_993]: (v5_pre_topc('#skF_4', A_993, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', A_993, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0(A_993), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_993), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_993), '#skF_4') | ~l1_pre_topc(A_993) | ~v2_pre_topc(A_993) | ~r1_tarski('#skF_4', u1_struct_0(A_993)))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_16134])).
% 17.05/9.36  tff(c_16157, plain, (v5_pre_topc('#skF_4', '#skF_2', g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_4', '#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), '#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~r1_tarski('#skF_4', u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_14157, c_16148])).
% 17.05/9.36  tff(c_16162, plain, (v5_pre_topc('#skF_4', '#skF_2', g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', '#skF_2', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_14157, c_74, c_72, c_14999, c_14157, c_14157, c_14923, c_16157])).
% 17.05/9.36  tff(c_16163, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(splitLeft, [status(thm)], [c_16162])).
% 17.05/9.36  tff(c_16166, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_14478, c_16163])).
% 17.05/9.36  tff(c_16170, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_16166])).
% 17.05/9.36  tff(c_16172, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(splitRight, [status(thm)], [c_16162])).
% 17.05/9.36  tff(c_14036, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_13979, c_162])).
% 17.05/9.36  tff(c_15034, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_14137, c_14036])).
% 17.05/9.36  tff(c_14293, plain, (![D_863, A_864, B_865]: (v5_pre_topc(D_863, A_864, B_865) | ~v5_pre_topc(D_863, A_864, g1_pre_topc(u1_struct_0(B_865), u1_pre_topc(B_865))) | ~m1_subset_1(D_863, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_864), u1_struct_0(g1_pre_topc(u1_struct_0(B_865), u1_pre_topc(B_865)))))) | ~v1_funct_2(D_863, u1_struct_0(A_864), u1_struct_0(g1_pre_topc(u1_struct_0(B_865), u1_pre_topc(B_865)))) | ~m1_subset_1(D_863, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_864), u1_struct_0(B_865)))) | ~v1_funct_2(D_863, u1_struct_0(A_864), u1_struct_0(B_865)) | ~v1_funct_1(D_863) | ~l1_pre_topc(B_865) | ~v2_pre_topc(B_865) | ~l1_pre_topc(A_864) | ~v2_pre_topc(A_864))), inference(cnfTransformation, [status(thm)], [f_163])).
% 17.05/9.36  tff(c_14299, plain, (![D_863, A_864]: (v5_pre_topc(D_863, A_864, '#skF_2') | ~v5_pre_topc(D_863, A_864, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_subset_1(D_863, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_864), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))))) | ~v1_funct_2(D_863, u1_struct_0(A_864), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1(D_863, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_864), u1_struct_0('#skF_2')))) | ~v1_funct_2(D_863, u1_struct_0(A_864), u1_struct_0('#skF_2')) | ~v1_funct_1(D_863) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(A_864) | ~v2_pre_topc(A_864))), inference(superposition, [status(thm), theory('equality')], [c_14157, c_14293])).
% 17.05/9.36  tff(c_16324, plain, (![D_1001, A_1002]: (v5_pre_topc(D_1001, A_1002, '#skF_2') | ~v5_pre_topc(D_1001, A_1002, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~m1_subset_1(D_1001, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1002), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))))) | ~v1_funct_2(D_1001, u1_struct_0(A_1002), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~m1_subset_1(D_1001, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1002), '#skF_4'))) | ~v1_funct_2(D_1001, u1_struct_0(A_1002), '#skF_4') | ~v1_funct_1(D_1001) | ~l1_pre_topc(A_1002) | ~v2_pre_topc(A_1002))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_14157, c_14157, c_14157, c_14157, c_14299])).
% 17.05/9.36  tff(c_16328, plain, (![A_1002]: (v5_pre_topc('#skF_4', A_1002, '#skF_2') | ~v5_pre_topc('#skF_4', A_1002, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1002), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1002), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1002), '#skF_4') | ~v1_funct_1('#skF_4') | ~l1_pre_topc(A_1002) | ~v2_pre_topc(A_1002) | ~r1_tarski('#skF_4', u1_struct_0(A_1002)))), inference(resolution, [status(thm)], [c_15072, c_16324])).
% 17.05/9.36  tff(c_16342, plain, (![A_1003]: (v5_pre_topc('#skF_4', A_1003, '#skF_2') | ~v5_pre_topc('#skF_4', A_1003, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1003), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1003), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1003), '#skF_4') | ~l1_pre_topc(A_1003) | ~v2_pre_topc(A_1003) | ~r1_tarski('#skF_4', u1_struct_0(A_1003)))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_16328])).
% 17.05/9.36  tff(c_16348, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', '#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~r1_tarski('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_14918, c_16342])).
% 17.05/9.36  tff(c_16354, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_14918, c_15899, c_15225, c_14999, c_14918, c_16172, c_14918, c_14923, c_15034, c_16348])).
% 17.05/9.36  tff(c_16356, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16101, c_16354])).
% 17.05/9.36  tff(c_16357, plain, (u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))='#skF_4'), inference(splitRight, [status(thm)], [c_14397])).
% 17.05/9.36  tff(c_16360, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16357, c_14149])).
% 17.05/9.36  tff(c_16555, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_14137, c_14036])).
% 17.05/9.36  tff(c_14252, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14246, c_50])).
% 17.05/9.36  tff(c_14275, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~l1_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_64, c_14252])).
% 17.05/9.36  tff(c_16899, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_14153, c_14151, c_14154, c_16357, c_14146, c_16357, c_16360, c_16357, c_16555, c_14275])).
% 17.05/9.36  tff(c_14303, plain, (![D_863, A_864]: (v5_pre_topc(D_863, A_864, '#skF_2') | ~v5_pre_topc(D_863, A_864, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~m1_subset_1(D_863, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_864), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))))) | ~v1_funct_2(D_863, u1_struct_0(A_864), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~m1_subset_1(D_863, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_864), '#skF_4'))) | ~v1_funct_2(D_863, u1_struct_0(A_864), '#skF_4') | ~v1_funct_1(D_863) | ~l1_pre_topc(A_864) | ~v2_pre_topc(A_864))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_14157, c_14157, c_14157, c_14157, c_14299])).
% 17.05/9.36  tff(c_17003, plain, (![D_1045, A_1046]: (v5_pre_topc(D_1045, A_1046, '#skF_2') | ~v5_pre_topc(D_1045, A_1046, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~m1_subset_1(D_1045, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1046), '#skF_4'))) | ~v1_funct_2(D_1045, u1_struct_0(A_1046), '#skF_4') | ~m1_subset_1(D_1045, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1046), '#skF_4'))) | ~v1_funct_2(D_1045, u1_struct_0(A_1046), '#skF_4') | ~v1_funct_1(D_1045) | ~l1_pre_topc(A_1046) | ~v2_pre_topc(A_1046))), inference(demodulation, [status(thm), theory('equality')], [c_16357, c_16357, c_14303])).
% 17.05/9.36  tff(c_17012, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4') | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14146, c_17003])).
% 17.05/9.36  tff(c_17026, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_64, c_14154, c_14146, c_16899, c_17012])).
% 17.05/9.36  tff(c_17028, plain, $false, inference(negUnitSimplification, [status(thm)], [c_194, c_17026])).
% 17.05/9.36  tff(c_17029, plain, (u1_struct_0('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_13914])).
% 17.05/9.36  tff(c_17037, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))))), inference(demodulation, [status(thm), theory('equality')], [c_17029, c_60])).
% 17.05/9.36  tff(c_17210, plain, (k1_relset_1(u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_17037, c_18])).
% 17.05/9.36  tff(c_17231, plain, (k1_relset_1(u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_13829, c_17210])).
% 17.05/9.36  tff(c_17039, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_17029, c_62])).
% 17.05/9.36  tff(c_17199, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0 | k1_relset_1(u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')=u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(resolution, [status(thm)], [c_17037, c_32])).
% 17.05/9.36  tff(c_17222, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0 | k1_relset_1(u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')=u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_17039, c_17199])).
% 17.05/9.36  tff(c_20538, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0 | u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1')))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_17231, c_17222])).
% 17.05/9.36  tff(c_20539, plain, (u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1')))=k1_xboole_0), inference(splitLeft, [status(thm)], [c_20538])).
% 17.05/9.36  tff(c_13910, plain, (r1_tarski(k1_xboole_0, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(resolution, [status(thm)], [c_143, c_13887])).
% 17.05/9.36  tff(c_17032, plain, (r1_tarski(k1_xboole_0, u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_17029, c_13910])).
% 17.05/9.36  tff(c_17136, plain, (u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1')))=k1_xboole_0 | ~r1_tarski(u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1'))), k1_xboole_0)), inference(resolution, [status(thm)], [c_17032, c_2])).
% 17.05/9.36  tff(c_17354, plain, (~r1_tarski(u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1'))), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_17136])).
% 17.05/9.36  tff(c_20541, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20539, c_17354])).
% 17.05/9.36  tff(c_20549, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_20541])).
% 17.05/9.36  tff(c_20551, plain, (u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1')))!=k1_xboole_0), inference(splitRight, [status(thm)], [c_20538])).
% 17.05/9.36  tff(c_20550, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0), inference(splitRight, [status(thm)], [c_20538])).
% 17.05/9.36  tff(c_20559, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1'))), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20550, c_17039])).
% 17.05/9.36  tff(c_20558, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1'))), k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_20550, c_17037])).
% 17.05/9.36  tff(c_20721, plain, (k1_xboole_0='#skF_4' | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1'))), k1_xboole_0) | u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1')))=k1_xboole_0), inference(resolution, [status(thm)], [c_20558, c_24])).
% 17.05/9.36  tff(c_20748, plain, (k1_xboole_0='#skF_4' | u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1')))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_20559, c_20721])).
% 17.05/9.36  tff(c_20749, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_20551, c_20748])).
% 17.05/9.36  tff(c_20766, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_20749, c_20550])).
% 17.05/9.36  tff(c_17038, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_17029, c_91])).
% 17.05/9.36  tff(c_20780, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_20749, c_17038])).
% 17.05/9.36  tff(c_13832, plain, (![B_117]: (k1_relset_1(B_117, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')=k1_xboole_0 | ~r1_tarski(k1_xboole_0, B_117))), inference(demodulation, [status(thm), theory('equality')], [c_13829, c_13829, c_342])).
% 17.05/9.36  tff(c_341, plain, (k1_relset_1(k1_xboole_0, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_4', k1_xboole_0, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~r1_tarski(k1_relat_1('#skF_4'), k1_xboole_0)), inference(resolution, [status(thm)], [c_312, c_30])).
% 17.05/9.36  tff(c_17483, plain, (k1_relset_1(k1_xboole_0, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_4', k1_xboole_0, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_13829, c_341])).
% 17.05/9.36  tff(c_17484, plain, (~v1_funct_2('#skF_4', k1_xboole_0, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(splitLeft, [status(thm)], [c_17483])).
% 17.05/9.36  tff(c_18498, plain, (v1_funct_2('#skF_4', k1_xboole_0, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | k1_relset_1(k1_xboole_0, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6, c_13829, c_340])).
% 17.05/9.36  tff(c_18499, plain, (k1_relset_1(k1_xboole_0, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_17484, c_18498])).
% 17.05/9.36  tff(c_18502, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_13832, c_18499])).
% 17.05/9.36  tff(c_18506, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_18502])).
% 17.05/9.36  tff(c_18508, plain, (v1_funct_2('#skF_4', k1_xboole_0, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(splitRight, [status(thm)], [c_17483])).
% 17.05/9.36  tff(c_20554, plain, (v1_funct_2('#skF_4', k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20550, c_18508])).
% 17.05/9.36  tff(c_20764, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20749, c_20749, c_20554])).
% 17.05/9.36  tff(c_17355, plain, (![B_1061]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_1061, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))))) | ~r1_tarski(k1_xboole_0, B_1061))), inference(demodulation, [status(thm), theory('equality')], [c_13829, c_200])).
% 17.05/9.36  tff(c_17405, plain, (![B_1061]: (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0 | v1_funct_2('#skF_4', B_1061, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | k1_relset_1(B_1061, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')!=B_1061 | ~r1_tarski(k1_xboole_0, B_1061))), inference(resolution, [status(thm)], [c_17355, c_28])).
% 17.05/9.36  tff(c_20802, plain, (![B_1061]: (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))='#skF_4' | v1_funct_2('#skF_4', B_1061, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | k1_relset_1(B_1061, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')!=B_1061 | ~r1_tarski('#skF_4', B_1061))), inference(demodulation, [status(thm), theory('equality')], [c_20749, c_20749, c_17405])).
% 17.05/9.36  tff(c_20803, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))='#skF_4'), inference(splitLeft, [status(thm)], [c_20802])).
% 17.05/9.36  tff(c_20787, plain, (u1_struct_0('#skF_1')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_20749, c_17029])).
% 17.05/9.36  tff(c_17040, plain, (v1_funct_2('#skF_4', k1_xboole_0, u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_17029, c_87])).
% 17.05/9.36  tff(c_20785, plain, (v1_funct_2('#skF_4', '#skF_4', u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_20749, c_17040])).
% 17.05/9.36  tff(c_20508, plain, (![D_1158, A_1159, B_1160]: (v5_pre_topc(D_1158, A_1159, B_1160) | ~v5_pre_topc(D_1158, A_1159, g1_pre_topc(u1_struct_0(B_1160), u1_pre_topc(B_1160))) | ~m1_subset_1(D_1158, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1159), u1_struct_0(g1_pre_topc(u1_struct_0(B_1160), u1_pre_topc(B_1160)))))) | ~v1_funct_2(D_1158, u1_struct_0(A_1159), u1_struct_0(g1_pre_topc(u1_struct_0(B_1160), u1_pre_topc(B_1160)))) | ~m1_subset_1(D_1158, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1159), u1_struct_0(B_1160)))) | ~v1_funct_2(D_1158, u1_struct_0(A_1159), u1_struct_0(B_1160)) | ~v1_funct_1(D_1158) | ~l1_pre_topc(B_1160) | ~v2_pre_topc(B_1160) | ~l1_pre_topc(A_1159) | ~v2_pre_topc(A_1159))), inference(cnfTransformation, [status(thm)], [f_163])).
% 17.05/9.36  tff(c_20512, plain, (![A_1159]: (v5_pre_topc('#skF_4', A_1159, '#skF_2') | ~v5_pre_topc('#skF_4', A_1159, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1159), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1159), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1159), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(A_1159) | ~v2_pre_topc(A_1159) | ~r1_tarski(k1_xboole_0, u1_struct_0(A_1159)))), inference(resolution, [status(thm)], [c_13834, c_20508])).
% 17.05/9.36  tff(c_20524, plain, (![A_1159]: (v5_pre_topc('#skF_4', A_1159, '#skF_2') | ~v5_pre_topc('#skF_4', A_1159, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1159), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1159), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1159), u1_struct_0('#skF_2')) | ~l1_pre_topc(A_1159) | ~v2_pre_topc(A_1159) | ~r1_tarski(k1_xboole_0, u1_struct_0(A_1159)))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_64, c_20512])).
% 17.05/9.36  tff(c_20943, plain, (![A_1167]: (v5_pre_topc('#skF_4', A_1167, '#skF_2') | ~v5_pre_topc('#skF_4', A_1167, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1167), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1167), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1167), u1_struct_0('#skF_2')) | ~l1_pre_topc(A_1167) | ~v2_pre_topc(A_1167) | ~r1_tarski('#skF_4', u1_struct_0(A_1167)))), inference(demodulation, [status(thm), theory('equality')], [c_20749, c_20524])).
% 17.05/9.36  tff(c_20946, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', '#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski('#skF_4', u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_20787, c_20943])).
% 17.05/9.36  tff(c_20948, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', '#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_20787, c_78, c_76, c_20785, c_20787, c_20787, c_20946])).
% 17.05/9.36  tff(c_20949, plain, (~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', '#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_194, c_20948])).
% 17.05/9.36  tff(c_21355, plain, (~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_20780, c_20764, c_20803, c_20949])).
% 17.05/9.36  tff(c_20779, plain, (r1_tarski('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_20749, c_20749, c_17032])).
% 17.05/9.36  tff(c_20556, plain, (![B_107]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_107, k1_xboole_0))) | ~r1_tarski(k1_xboole_0, B_107))), inference(demodulation, [status(thm), theory('equality')], [c_20550, c_13834])).
% 17.05/9.36  tff(c_20759, plain, (![B_107]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_107, '#skF_4'))) | ~r1_tarski('#skF_4', B_107))), inference(demodulation, [status(thm), theory('equality')], [c_20749, c_20749, c_20556])).
% 17.05/9.36  tff(c_20761, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20749, c_20749, c_20559])).
% 17.05/9.36  tff(c_20758, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_20749, c_20749, c_20558])).
% 17.05/9.36  tff(c_17137, plain, (![D_1050, A_1051, B_1052]: (v5_pre_topc(D_1050, A_1051, B_1052) | ~v5_pre_topc(D_1050, g1_pre_topc(u1_struct_0(A_1051), u1_pre_topc(A_1051)), B_1052) | ~m1_subset_1(D_1050, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1051), u1_pre_topc(A_1051))), u1_struct_0(B_1052)))) | ~v1_funct_2(D_1050, u1_struct_0(g1_pre_topc(u1_struct_0(A_1051), u1_pre_topc(A_1051))), u1_struct_0(B_1052)) | ~m1_subset_1(D_1050, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1051), u1_struct_0(B_1052)))) | ~v1_funct_2(D_1050, u1_struct_0(A_1051), u1_struct_0(B_1052)) | ~v1_funct_1(D_1050) | ~l1_pre_topc(B_1052) | ~v2_pre_topc(B_1052) | ~l1_pre_topc(A_1051) | ~v2_pre_topc(A_1051))), inference(cnfTransformation, [status(thm)], [f_134])).
% 17.05/9.36  tff(c_17140, plain, (![D_1050, B_1052]: (v5_pre_topc(D_1050, '#skF_1', B_1052) | ~v5_pre_topc(D_1050, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_1052) | ~m1_subset_1(D_1050, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1'))), u1_struct_0(B_1052)))) | ~v1_funct_2(D_1050, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_1052)) | ~m1_subset_1(D_1050, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_1052)))) | ~v1_funct_2(D_1050, u1_struct_0('#skF_1'), u1_struct_0(B_1052)) | ~v1_funct_1(D_1050) | ~l1_pre_topc(B_1052) | ~v2_pre_topc(B_1052) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_17029, c_17137])).
% 17.05/9.36  tff(c_17145, plain, (![D_1050, B_1052]: (v5_pre_topc(D_1050, '#skF_1', B_1052) | ~v5_pre_topc(D_1050, g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1')), B_1052) | ~m1_subset_1(D_1050, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1'))), u1_struct_0(B_1052)))) | ~v1_funct_2(D_1050, u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1'))), u1_struct_0(B_1052)) | ~m1_subset_1(D_1050, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, u1_struct_0(B_1052)))) | ~v1_funct_2(D_1050, k1_xboole_0, u1_struct_0(B_1052)) | ~v1_funct_1(D_1050) | ~l1_pre_topc(B_1052) | ~v2_pre_topc(B_1052))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_17029, c_17029, c_17029, c_17029, c_17140])).
% 17.05/9.36  tff(c_21498, plain, (![D_1191, B_1192]: (v5_pre_topc(D_1191, '#skF_1', B_1192) | ~v5_pre_topc(D_1191, g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), B_1192) | ~m1_subset_1(D_1191, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), u1_struct_0(B_1192)))) | ~v1_funct_2(D_1191, u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), u1_struct_0(B_1192)) | ~m1_subset_1(D_1191, k1_zfmisc_1(k2_zfmisc_1('#skF_4', u1_struct_0(B_1192)))) | ~v1_funct_2(D_1191, '#skF_4', u1_struct_0(B_1192)) | ~v1_funct_1(D_1191) | ~l1_pre_topc(B_1192) | ~v2_pre_topc(B_1192))), inference(demodulation, [status(thm), theory('equality')], [c_20749, c_20749, c_20749, c_20749, c_20749, c_17145])).
% 17.05/9.36  tff(c_21508, plain, (![D_1191]: (v5_pre_topc(D_1191, '#skF_1', '#skF_1') | ~v5_pre_topc(D_1191, g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), '#skF_1') | ~m1_subset_1(D_1191, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), '#skF_4'))) | ~v1_funct_2(D_1191, u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), u1_struct_0('#skF_1')) | ~m1_subset_1(D_1191, k1_zfmisc_1(k2_zfmisc_1('#skF_4', u1_struct_0('#skF_1')))) | ~v1_funct_2(D_1191, '#skF_4', u1_struct_0('#skF_1')) | ~v1_funct_1(D_1191) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_20787, c_21498])).
% 17.05/9.36  tff(c_21621, plain, (![D_1203]: (v5_pre_topc(D_1203, '#skF_1', '#skF_1') | ~v5_pre_topc(D_1203, g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), '#skF_1') | ~m1_subset_1(D_1203, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), '#skF_4'))) | ~v1_funct_2(D_1203, u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), '#skF_4') | ~m1_subset_1(D_1203, k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4'))) | ~v1_funct_2(D_1203, '#skF_4', '#skF_4') | ~v1_funct_1(D_1203))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_20787, c_20787, c_20787, c_21508])).
% 17.05/9.36  tff(c_21624, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_1') | ~v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), '#skF_1') | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4'))) | ~v1_funct_2('#skF_4', '#skF_4', '#skF_4') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_20758, c_21621])).
% 17.05/9.36  tff(c_21631, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_1') | ~v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), '#skF_1') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_20764, c_20761, c_21624])).
% 17.05/9.36  tff(c_21635, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(splitLeft, [status(thm)], [c_21631])).
% 17.05/9.36  tff(c_21650, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_20759, c_21635])).
% 17.05/9.36  tff(c_21654, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_21650])).
% 17.05/9.36  tff(c_21656, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(splitRight, [status(thm)], [c_21631])).
% 17.05/9.36  tff(c_17034, plain, (v5_pre_topc('#skF_4', g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_17029, c_162])).
% 17.05/9.36  tff(c_20773, plain, (v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_20749, c_17034])).
% 17.05/9.36  tff(c_17363, plain, (![A_28]: (v5_pre_topc('#skF_4', A_28, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_28), u1_pre_topc(A_28)), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_28), u1_pre_topc(A_28))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_28), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))))) | ~v1_funct_2('#skF_4', u1_struct_0(A_28), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_28) | ~v2_pre_topc(A_28) | ~r1_tarski(k1_xboole_0, u1_struct_0(g1_pre_topc(u1_struct_0(A_28), u1_pre_topc(A_28)))))), inference(resolution, [status(thm)], [c_17355, c_50])).
% 17.05/9.36  tff(c_17400, plain, (![A_28]: (v5_pre_topc('#skF_4', A_28, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_28), u1_pre_topc(A_28)), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_28), u1_pre_topc(A_28))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_28), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))))) | ~v1_funct_2('#skF_4', u1_struct_0(A_28), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_28) | ~v2_pre_topc(A_28) | ~r1_tarski(k1_xboole_0, u1_struct_0(g1_pre_topc(u1_struct_0(A_28), u1_pre_topc(A_28)))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_17363])).
% 17.05/9.36  tff(c_21300, plain, (![A_28]: (v5_pre_topc('#skF_4', A_28, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_28), u1_pre_topc(A_28)), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_28), u1_pre_topc(A_28))), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_28), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_28), '#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_28) | ~v2_pre_topc(A_28) | ~r1_tarski('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_28), u1_pre_topc(A_28)))))), inference(demodulation, [status(thm), theory('equality')], [c_20749, c_20803, c_20803, c_20803, c_17400])).
% 17.05/9.36  tff(c_21301, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_21300])).
% 17.05/9.36  tff(c_21304, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_46, c_21301])).
% 17.05/9.36  tff(c_21308, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_21304])).
% 17.05/9.36  tff(c_21310, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_21300])).
% 17.05/9.36  tff(c_17440, plain, (![D_1063, A_1064, B_1065]: (v5_pre_topc(D_1063, g1_pre_topc(u1_struct_0(A_1064), u1_pre_topc(A_1064)), B_1065) | ~v5_pre_topc(D_1063, A_1064, B_1065) | ~m1_subset_1(D_1063, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1064), u1_pre_topc(A_1064))), u1_struct_0(B_1065)))) | ~v1_funct_2(D_1063, u1_struct_0(g1_pre_topc(u1_struct_0(A_1064), u1_pre_topc(A_1064))), u1_struct_0(B_1065)) | ~m1_subset_1(D_1063, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1064), u1_struct_0(B_1065)))) | ~v1_funct_2(D_1063, u1_struct_0(A_1064), u1_struct_0(B_1065)) | ~v1_funct_1(D_1063) | ~l1_pre_topc(B_1065) | ~v2_pre_topc(B_1065) | ~l1_pre_topc(A_1064) | ~v2_pre_topc(A_1064))), inference(cnfTransformation, [status(thm)], [f_134])).
% 17.05/9.36  tff(c_17444, plain, (![A_1064]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_1064), u1_pre_topc(A_1064)), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', A_1064, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_1064), u1_pre_topc(A_1064))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1064), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1064), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_1064) | ~v2_pre_topc(A_1064) | ~r1_tarski(k1_xboole_0, u1_struct_0(g1_pre_topc(u1_struct_0(A_1064), u1_pre_topc(A_1064)))))), inference(resolution, [status(thm)], [c_13834, c_17440])).
% 17.05/9.36  tff(c_17457, plain, (![A_1064]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_1064), u1_pre_topc(A_1064)), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', A_1064, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_1064), u1_pre_topc(A_1064))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1064), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1064), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_1064) | ~v2_pre_topc(A_1064) | ~r1_tarski(k1_xboole_0, u1_struct_0(g1_pre_topc(u1_struct_0(A_1064), u1_pre_topc(A_1064)))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_17444])).
% 17.05/9.36  tff(c_21343, plain, (![A_1064]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_1064), u1_pre_topc(A_1064)), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', A_1064, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_1064), u1_pre_topc(A_1064))), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1064), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1064), '#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_1064) | ~v2_pre_topc(A_1064) | ~r1_tarski('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_1064), u1_pre_topc(A_1064)))))), inference(demodulation, [status(thm), theory('equality')], [c_20749, c_21310, c_20803, c_20803, c_20803, c_17457])).
% 17.05/9.36  tff(c_21344, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_21343])).
% 17.05/9.36  tff(c_21347, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_120, c_21344])).
% 17.05/9.36  tff(c_21351, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_21347])).
% 17.05/9.36  tff(c_21353, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_21343])).
% 17.05/9.36  tff(c_21309, plain, (![A_28]: (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | v5_pre_topc('#skF_4', A_28, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_28), u1_pre_topc(A_28)), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_28), u1_pre_topc(A_28))), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_28), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_28), '#skF_4') | ~l1_pre_topc(A_28) | ~v2_pre_topc(A_28) | ~r1_tarski('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_28), u1_pre_topc(A_28)))))), inference(splitRight, [status(thm)], [c_21300])).
% 17.05/9.36  tff(c_21922, plain, (![A_1225]: (v5_pre_topc('#skF_4', A_1225, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_1225), u1_pre_topc(A_1225)), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_1225), u1_pre_topc(A_1225))), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1225), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1225), '#skF_4') | ~l1_pre_topc(A_1225) | ~v2_pre_topc(A_1225) | ~r1_tarski('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_1225), u1_pre_topc(A_1225)))))), inference(demodulation, [status(thm), theory('equality')], [c_21353, c_21309])).
% 17.05/9.36  tff(c_21934, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_20787, c_21922])).
% 17.05/9.36  tff(c_21941, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_20779, c_20787, c_78, c_76, c_20764, c_20787, c_21656, c_20787, c_20761, c_20787, c_20773, c_21934])).
% 17.05/9.36  tff(c_21943, plain, $false, inference(negUnitSimplification, [status(thm)], [c_21355, c_21941])).
% 17.05/9.36  tff(c_21945, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))!='#skF_4'), inference(splitRight, [status(thm)], [c_20802])).
% 17.05/9.36  tff(c_22227, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20766, c_21945])).
% 17.05/9.36  tff(c_22228, plain, (u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1')))=k1_xboole_0), inference(splitRight, [status(thm)], [c_17136])).
% 17.05/9.36  tff(c_17047, plain, (v2_pre_topc(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_17029, c_46])).
% 17.05/9.36  tff(c_17060, plain, (v2_pre_topc(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_17047])).
% 17.05/9.36  tff(c_17053, plain, (l1_pre_topc(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_17029, c_120])).
% 17.05/9.36  tff(c_17064, plain, (l1_pre_topc(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_17053])).
% 17.05/9.36  tff(c_22233, plain, (v1_funct_2('#skF_4', k1_xboole_0, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_22228, c_17039])).
% 17.05/9.36  tff(c_22464, plain, (![D_1236, A_1237, B_1238]: (v5_pre_topc(D_1236, A_1237, B_1238) | ~v5_pre_topc(D_1236, A_1237, g1_pre_topc(u1_struct_0(B_1238), u1_pre_topc(B_1238))) | ~m1_subset_1(D_1236, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1237), u1_struct_0(g1_pre_topc(u1_struct_0(B_1238), u1_pre_topc(B_1238)))))) | ~v1_funct_2(D_1236, u1_struct_0(A_1237), u1_struct_0(g1_pre_topc(u1_struct_0(B_1238), u1_pre_topc(B_1238)))) | ~m1_subset_1(D_1236, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1237), u1_struct_0(B_1238)))) | ~v1_funct_2(D_1236, u1_struct_0(A_1237), u1_struct_0(B_1238)) | ~v1_funct_1(D_1236) | ~l1_pre_topc(B_1238) | ~v2_pre_topc(B_1238) | ~l1_pre_topc(A_1237) | ~v2_pre_topc(A_1237))), inference(cnfTransformation, [status(thm)], [f_163])).
% 17.05/9.36  tff(c_22468, plain, (![A_1237]: (v5_pre_topc('#skF_4', A_1237, '#skF_2') | ~v5_pre_topc('#skF_4', A_1237, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1237), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1237), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1237), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(A_1237) | ~v2_pre_topc(A_1237) | ~r1_tarski(k1_xboole_0, u1_struct_0(A_1237)))), inference(resolution, [status(thm)], [c_13834, c_22464])).
% 17.05/9.36  tff(c_27088, plain, (![A_1385]: (v5_pre_topc('#skF_4', A_1385, '#skF_2') | ~v5_pre_topc('#skF_4', A_1385, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1385), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1385), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1385), u1_struct_0('#skF_2')) | ~l1_pre_topc(A_1385) | ~v2_pre_topc(A_1385) | ~r1_tarski(k1_xboole_0, u1_struct_0(A_1385)))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_64, c_22468])).
% 17.05/9.36  tff(c_27094, plain, (v5_pre_topc('#skF_4', g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1')), '#skF_2') | ~v5_pre_topc('#skF_4', g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', k1_xboole_0, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1'))), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1'))), u1_struct_0('#skF_2')) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1'))) | ~r1_tarski(k1_xboole_0, u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_22228, c_27088])).
% 17.05/9.36  tff(c_27100, plain, (v5_pre_topc('#skF_4', g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_22228, c_17060, c_17064, c_17040, c_22228, c_17038, c_22228, c_22233, c_17034, c_27094])).
% 17.05/9.36  tff(c_17267, plain, (![B_1056]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_1056, u1_struct_0('#skF_2')))) | ~r1_tarski(k1_xboole_0, B_1056))), inference(demodulation, [status(thm), theory('equality')], [c_13829, c_201])).
% 17.05/9.36  tff(c_17271, plain, (![A_28]: (v5_pre_topc('#skF_4', A_28, '#skF_2') | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_28), u1_pre_topc(A_28)), '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_28), u1_pre_topc(A_28))), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_28), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0(A_28), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(A_28) | ~v2_pre_topc(A_28) | ~r1_tarski(k1_xboole_0, u1_struct_0(g1_pre_topc(u1_struct_0(A_28), u1_pre_topc(A_28)))))), inference(resolution, [status(thm)], [c_17267, c_50])).
% 17.05/9.36  tff(c_27200, plain, (![A_1393]: (v5_pre_topc('#skF_4', A_1393, '#skF_2') | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_1393), u1_pre_topc(A_1393)), '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_1393), u1_pre_topc(A_1393))), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1393), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1393), u1_struct_0('#skF_2')) | ~l1_pre_topc(A_1393) | ~v2_pre_topc(A_1393) | ~r1_tarski(k1_xboole_0, u1_struct_0(g1_pre_topc(u1_struct_0(A_1393), u1_pre_topc(A_1393)))))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_64, c_17271])).
% 17.05/9.36  tff(c_27209, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1'))), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(k1_xboole_0, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_17029, c_27200])).
% 17.05/9.36  tff(c_27214, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_22228, c_17029, c_78, c_76, c_17040, c_17029, c_17038, c_17029, c_17040, c_22228, c_27100, c_17029, c_27209])).
% 17.05/9.36  tff(c_27216, plain, $false, inference(negUnitSimplification, [status(thm)], [c_194, c_27214])).
% 17.05/9.37  tff(c_27218, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_88])).
% 17.05/9.37  tff(c_27441, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_27439, c_27218])).
% 17.05/9.37  tff(c_27446, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_27439, c_62])).
% 17.05/9.37  tff(c_27228, plain, (k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_27221])).
% 17.05/9.37  tff(c_27534, plain, (k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_27439, c_27228])).
% 17.05/9.37  tff(c_27444, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))))), inference(demodulation, [status(thm), theory('equality')], [c_27439, c_60])).
% 17.05/9.37  tff(c_27561, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0 | k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')=u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(resolution, [status(thm)], [c_27444, c_32])).
% 17.05/9.37  tff(c_27583, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0 | u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_27446, c_27534, c_27561])).
% 17.05/9.37  tff(c_27596, plain, (u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_27583])).
% 17.05/9.37  tff(c_27453, plain, (v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_27439, c_46])).
% 17.05/9.37  tff(c_27466, plain, (v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_27453])).
% 17.05/9.37  tff(c_27459, plain, (l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_27439, c_120])).
% 17.05/9.37  tff(c_27470, plain, (l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_27459])).
% 17.05/9.37  tff(c_27447, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_27439, c_87])).
% 17.05/9.37  tff(c_27445, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_27439, c_91])).
% 17.05/9.37  tff(c_27600, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_27596, c_27446])).
% 17.05/9.37  tff(c_27217, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_88])).
% 17.05/9.37  tff(c_30715, plain, (![D_1657, A_1658, B_1659]: (v5_pre_topc(D_1657, g1_pre_topc(u1_struct_0(A_1658), u1_pre_topc(A_1658)), B_1659) | ~v5_pre_topc(D_1657, A_1658, B_1659) | ~m1_subset_1(D_1657, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1658), u1_pre_topc(A_1658))), u1_struct_0(B_1659)))) | ~v1_funct_2(D_1657, u1_struct_0(g1_pre_topc(u1_struct_0(A_1658), u1_pre_topc(A_1658))), u1_struct_0(B_1659)) | ~m1_subset_1(D_1657, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1658), u1_struct_0(B_1659)))) | ~v1_funct_2(D_1657, u1_struct_0(A_1658), u1_struct_0(B_1659)) | ~v1_funct_1(D_1657) | ~l1_pre_topc(B_1659) | ~v2_pre_topc(B_1659) | ~l1_pre_topc(A_1658) | ~v2_pre_topc(A_1658))), inference(cnfTransformation, [status(thm)], [f_134])).
% 17.05/9.37  tff(c_30724, plain, (![D_1657, B_1659]: (v5_pre_topc(D_1657, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_1659) | ~v5_pre_topc(D_1657, '#skF_1', B_1659) | ~m1_subset_1(D_1657, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(B_1659)))) | ~v1_funct_2(D_1657, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_1659)) | ~m1_subset_1(D_1657, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_1659)))) | ~v1_funct_2(D_1657, u1_struct_0('#skF_1'), u1_struct_0(B_1659)) | ~v1_funct_1(D_1657) | ~l1_pre_topc(B_1659) | ~v2_pre_topc(B_1659) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_27439, c_30715])).
% 17.05/9.37  tff(c_30810, plain, (![D_1664, B_1665]: (v5_pre_topc(D_1664, g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), B_1665) | ~v5_pre_topc(D_1664, '#skF_1', B_1665) | ~m1_subset_1(D_1664, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_1665)))) | ~v1_funct_2(D_1664, k1_relat_1('#skF_4'), u1_struct_0(B_1665)) | ~v1_funct_1(D_1664) | ~l1_pre_topc(B_1665) | ~v2_pre_topc(B_1665))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_27439, c_27439, c_27596, c_27439, c_27596, c_27439, c_30724])).
% 17.05/9.37  tff(c_30819, plain, (v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), '#skF_2') | ~v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_27445, c_30810])).
% 17.05/9.37  tff(c_30839, plain, (v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_64, c_27447, c_27217, c_30819])).
% 17.05/9.37  tff(c_27256, plain, (![B_1408]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_1408, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))))) | ~r1_tarski(k1_relat_1('#skF_4'), B_1408))), inference(resolution, [status(thm)], [c_60, c_27251])).
% 17.05/9.37  tff(c_30849, plain, (![D_1666, A_1667, B_1668]: (v5_pre_topc(D_1666, A_1667, g1_pre_topc(u1_struct_0(B_1668), u1_pre_topc(B_1668))) | ~v5_pre_topc(D_1666, A_1667, B_1668) | ~m1_subset_1(D_1666, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1667), u1_struct_0(g1_pre_topc(u1_struct_0(B_1668), u1_pre_topc(B_1668)))))) | ~v1_funct_2(D_1666, u1_struct_0(A_1667), u1_struct_0(g1_pre_topc(u1_struct_0(B_1668), u1_pre_topc(B_1668)))) | ~m1_subset_1(D_1666, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1667), u1_struct_0(B_1668)))) | ~v1_funct_2(D_1666, u1_struct_0(A_1667), u1_struct_0(B_1668)) | ~v1_funct_1(D_1666) | ~l1_pre_topc(B_1668) | ~v2_pre_topc(B_1668) | ~l1_pre_topc(A_1667) | ~v2_pre_topc(A_1667))), inference(cnfTransformation, [status(thm)], [f_163])).
% 17.05/9.37  tff(c_30865, plain, (![A_1667]: (v5_pre_topc('#skF_4', A_1667, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', A_1667, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0(A_1667), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1667), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1667), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(A_1667) | ~v2_pre_topc(A_1667) | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(A_1667)))), inference(resolution, [status(thm)], [c_27256, c_30849])).
% 17.05/9.37  tff(c_30879, plain, (![A_1669]: (v5_pre_topc('#skF_4', A_1669, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', A_1669, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0(A_1669), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1669), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1669), u1_struct_0('#skF_2')) | ~l1_pre_topc(A_1669) | ~v2_pre_topc(A_1669) | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(A_1669)))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_64, c_30865])).
% 17.05/9.37  tff(c_30885, plain, (v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), '#skF_2') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0('#skF_2')) | ~l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))) | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_27596, c_30879])).
% 17.05/9.37  tff(c_30891, plain, (v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_27596, c_27466, c_27470, c_27447, c_27596, c_27445, c_27596, c_27600, c_30839, c_30885])).
% 17.05/9.37  tff(c_30893, plain, $false, inference(negUnitSimplification, [status(thm)], [c_27441, c_30891])).
% 17.05/9.37  tff(c_30894, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0), inference(splitRight, [status(thm)], [c_27583])).
% 17.05/9.37  tff(c_30899, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_30894, c_27446])).
% 17.05/9.37  tff(c_30896, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_30894, c_27444])).
% 17.05/9.37  tff(c_31041, plain, (k1_xboole_0='#skF_4' | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), k1_xboole_0) | u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))=k1_xboole_0), inference(resolution, [status(thm)], [c_30896, c_24])).
% 17.05/9.37  tff(c_31067, plain, (k1_xboole_0='#skF_4' | u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30899, c_31041])).
% 17.05/9.37  tff(c_31075, plain, (u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))=k1_xboole_0), inference(splitLeft, [status(thm)], [c_31067])).
% 17.05/9.37  tff(c_27442, plain, (v4_relat_1('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_27439, c_143])).
% 17.05/9.37  tff(c_31079, plain, (v4_relat_1('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_31075, c_27442])).
% 17.05/9.37  tff(c_31081, plain, $false, inference(negUnitSimplification, [status(thm)], [c_27416, c_31079])).
% 17.05/9.37  tff(c_31082, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_31067])).
% 17.05/9.37  tff(c_30900, plain, (![B_1408]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_1408, k1_xboole_0))) | ~r1_tarski(k1_relat_1('#skF_4'), B_1408))), inference(demodulation, [status(thm), theory('equality')], [c_30894, c_27256])).
% 17.05/9.37  tff(c_31088, plain, (![B_1408]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_1408, '#skF_4'))) | ~r1_tarski(k1_relat_1('#skF_4'), B_1408))), inference(demodulation, [status(thm), theory('equality')], [c_31082, c_30900])).
% 17.05/9.37  tff(c_31306, plain, (![A_1685]: (v1_funct_2('#skF_4', A_1685, '#skF_4') | A_1685='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_1685, '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_31082, c_31082, c_31082, c_31082, c_31082, c_22])).
% 17.05/9.37  tff(c_31341, plain, (![B_1689]: (v1_funct_2('#skF_4', B_1689, '#skF_4') | B_1689='#skF_4' | ~r1_tarski(k1_relat_1('#skF_4'), B_1689))), inference(resolution, [status(thm)], [c_31088, c_31306])).
% 17.05/9.37  tff(c_31353, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_4') | k1_relat_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_6, c_31341])).
% 17.05/9.37  tff(c_31354, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(splitLeft, [status(thm)], [c_31353])).
% 17.05/9.37  tff(c_31095, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_31082, c_27410])).
% 17.05/9.37  tff(c_31364, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_31354, c_31095])).
% 17.05/9.37  tff(c_31384, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_31364])).
% 17.05/9.37  tff(c_31385, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_31353])).
% 17.05/9.37  tff(c_30970, plain, (![D_1671, A_1672, B_1673]: (v5_pre_topc(D_1671, A_1672, g1_pre_topc(u1_struct_0(B_1673), u1_pre_topc(B_1673))) | ~v5_pre_topc(D_1671, A_1672, B_1673) | ~m1_subset_1(D_1671, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1672), u1_struct_0(g1_pre_topc(u1_struct_0(B_1673), u1_pre_topc(B_1673)))))) | ~v1_funct_2(D_1671, u1_struct_0(A_1672), u1_struct_0(g1_pre_topc(u1_struct_0(B_1673), u1_pre_topc(B_1673)))) | ~m1_subset_1(D_1671, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1672), u1_struct_0(B_1673)))) | ~v1_funct_2(D_1671, u1_struct_0(A_1672), u1_struct_0(B_1673)) | ~v1_funct_1(D_1671) | ~l1_pre_topc(B_1673) | ~v2_pre_topc(B_1673) | ~l1_pre_topc(A_1672) | ~v2_pre_topc(A_1672))), inference(cnfTransformation, [status(thm)], [f_163])).
% 17.05/9.37  tff(c_30979, plain, (![D_1671, A_1672]: (v5_pre_topc(D_1671, A_1672, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc(D_1671, A_1672, '#skF_2') | ~m1_subset_1(D_1671, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1672), k1_xboole_0))) | ~v1_funct_2(D_1671, u1_struct_0(A_1672), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1(D_1671, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1672), u1_struct_0('#skF_2')))) | ~v1_funct_2(D_1671, u1_struct_0(A_1672), u1_struct_0('#skF_2')) | ~v1_funct_1(D_1671) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(A_1672) | ~v2_pre_topc(A_1672))), inference(superposition, [status(thm), theory('equality')], [c_30894, c_30970])).
% 17.05/9.37  tff(c_30989, plain, (![D_1671, A_1672]: (v5_pre_topc(D_1671, A_1672, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc(D_1671, A_1672, '#skF_2') | ~m1_subset_1(D_1671, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1672), k1_xboole_0))) | ~v1_funct_2(D_1671, u1_struct_0(A_1672), k1_xboole_0) | ~m1_subset_1(D_1671, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1672), u1_struct_0('#skF_2')))) | ~v1_funct_2(D_1671, u1_struct_0(A_1672), u1_struct_0('#skF_2')) | ~v1_funct_1(D_1671) | ~l1_pre_topc(A_1672) | ~v2_pre_topc(A_1672))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_30894, c_30979])).
% 17.05/9.37  tff(c_31965, plain, (![D_1722, A_1723]: (v5_pre_topc(D_1722, A_1723, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc(D_1722, A_1723, '#skF_2') | ~m1_subset_1(D_1722, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1723), '#skF_4'))) | ~v1_funct_2(D_1722, u1_struct_0(A_1723), '#skF_4') | ~m1_subset_1(D_1722, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1723), u1_struct_0('#skF_2')))) | ~v1_funct_2(D_1722, u1_struct_0(A_1723), u1_struct_0('#skF_2')) | ~v1_funct_1(D_1722) | ~l1_pre_topc(A_1723) | ~v2_pre_topc(A_1723))), inference(demodulation, [status(thm), theory('equality')], [c_31082, c_31082, c_30989])).
% 17.05/9.37  tff(c_31971, plain, (![D_1722]: (v5_pre_topc(D_1722, '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc(D_1722, '#skF_1', '#skF_2') | ~m1_subset_1(D_1722, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), '#skF_4'))) | ~v1_funct_2(D_1722, u1_struct_0('#skF_1'), '#skF_4') | ~m1_subset_1(D_1722, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(D_1722, u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(D_1722) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_27439, c_31965])).
% 17.05/9.37  tff(c_32099, plain, (![D_1727]: (v5_pre_topc(D_1727, '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc(D_1727, '#skF_1', '#skF_2') | ~m1_subset_1(D_1727, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_4'))) | ~v1_funct_2(D_1727, k1_relat_1('#skF_4'), '#skF_4') | ~m1_subset_1(D_1727, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(D_1727, k1_relat_1('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(D_1727))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_27439, c_27439, c_27439, c_31971])).
% 17.05/9.37  tff(c_32102, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_4'))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_4') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_27445, c_32099])).
% 17.05/9.37  tff(c_32109, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_27447, c_31385, c_27217, c_32102])).
% 17.05/9.37  tff(c_32113, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_4')))), inference(splitLeft, [status(thm)], [c_32109])).
% 17.05/9.37  tff(c_32127, plain, (~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_31088, c_32113])).
% 17.05/9.37  tff(c_32131, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_32127])).
% 17.05/9.37  tff(c_32133, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_4')))), inference(splitRight, [status(thm)], [c_32109])).
% 17.05/9.37  tff(c_31089, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_31082, c_30899])).
% 17.05/9.37  tff(c_31084, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_31082, c_30896])).
% 17.05/9.37  tff(c_32132, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_32109])).
% 17.05/9.37  tff(c_30908, plain, (v1_pre_topc(g1_pre_topc(k1_xboole_0, u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_30894, c_149])).
% 17.05/9.37  tff(c_31432, plain, (v1_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_31082, c_30908])).
% 17.05/9.37  tff(c_31433, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_31432])).
% 17.05/9.37  tff(c_31437, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_120, c_31433])).
% 17.05/9.37  tff(c_31441, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_31437])).
% 17.05/9.37  tff(c_31443, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_31432])).
% 17.05/9.37  tff(c_30905, plain, (v2_pre_topc(g1_pre_topc(k1_xboole_0, u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_30894, c_46])).
% 17.05/9.37  tff(c_31949, plain, (v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_31443, c_31082, c_30905])).
% 17.05/9.37  tff(c_31950, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_31949])).
% 17.05/9.37  tff(c_31954, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_46, c_31950])).
% 17.05/9.37  tff(c_31958, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_31954])).
% 17.05/9.37  tff(c_31960, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_31949])).
% 17.05/9.37  tff(c_31091, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_31082, c_30894])).
% 17.05/9.37  tff(c_31208, plain, (![D_1681, A_1682, B_1683]: (v5_pre_topc(D_1681, g1_pre_topc(u1_struct_0(A_1682), u1_pre_topc(A_1682)), B_1683) | ~v5_pre_topc(D_1681, A_1682, B_1683) | ~m1_subset_1(D_1681, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1682), u1_pre_topc(A_1682))), u1_struct_0(B_1683)))) | ~v1_funct_2(D_1681, u1_struct_0(g1_pre_topc(u1_struct_0(A_1682), u1_pre_topc(A_1682))), u1_struct_0(B_1683)) | ~m1_subset_1(D_1681, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1682), u1_struct_0(B_1683)))) | ~v1_funct_2(D_1681, u1_struct_0(A_1682), u1_struct_0(B_1683)) | ~v1_funct_1(D_1681) | ~l1_pre_topc(B_1683) | ~v2_pre_topc(B_1683) | ~l1_pre_topc(A_1682) | ~v2_pre_topc(A_1682))), inference(cnfTransformation, [status(thm)], [f_134])).
% 17.05/9.37  tff(c_31220, plain, (![D_1681, B_1683]: (v5_pre_topc(D_1681, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_1683) | ~v5_pre_topc(D_1681, '#skF_1', B_1683) | ~m1_subset_1(D_1681, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(B_1683)))) | ~v1_funct_2(D_1681, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_1683)) | ~m1_subset_1(D_1681, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_1683)))) | ~v1_funct_2(D_1681, u1_struct_0('#skF_1'), u1_struct_0(B_1683)) | ~v1_funct_1(D_1681) | ~l1_pre_topc(B_1683) | ~v2_pre_topc(B_1683) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_27439, c_31208])).
% 17.05/9.37  tff(c_32487, plain, (![D_1766, B_1767]: (v5_pre_topc(D_1766, g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), B_1767) | ~v5_pre_topc(D_1766, '#skF_1', B_1767) | ~m1_subset_1(D_1766, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(B_1767)))) | ~v1_funct_2(D_1766, u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(B_1767)) | ~m1_subset_1(D_1766, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_1767)))) | ~v1_funct_2(D_1766, k1_relat_1('#skF_4'), u1_struct_0(B_1767)) | ~v1_funct_1(D_1766) | ~l1_pre_topc(B_1767) | ~v2_pre_topc(B_1767))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_27439, c_27439, c_27439, c_27439, c_31220])).
% 17.05/9.37  tff(c_32490, plain, (![D_1766]: (v5_pre_topc(D_1766, g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc(D_1766, '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_subset_1(D_1766, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), '#skF_4'))) | ~v1_funct_2(D_1766, u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1(D_1766, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))))) | ~v1_funct_2(D_1766, k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~v1_funct_1(D_1766) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_31091, c_32487])).
% 17.05/9.37  tff(c_32586, plain, (![D_1774]: (v5_pre_topc(D_1774, g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc(D_1774, '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_subset_1(D_1774, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), '#skF_4'))) | ~v1_funct_2(D_1774, u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), '#skF_4') | ~m1_subset_1(D_1774, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_4'))) | ~v1_funct_2(D_1774, k1_relat_1('#skF_4'), '#skF_4') | ~v1_funct_1(D_1774))), inference(demodulation, [status(thm), theory('equality')], [c_31960, c_31443, c_31091, c_31091, c_31091, c_32490])).
% 17.05/9.37  tff(c_32596, plain, (~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_4'))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_4') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_32586, c_27441])).
% 17.05/9.37  tff(c_32604, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_31385, c_32133, c_31089, c_31084, c_32132, c_32596])).
% 17.05/9.37  tff(c_32605, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_27438])).
% 17.05/9.37  tff(c_32620, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32605, c_87])).
% 17.05/9.37  tff(c_32618, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_32605, c_91])).
% 17.05/9.37  tff(c_32711, plain, (k1_xboole_0='#skF_4' | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), k1_xboole_0) | u1_struct_0('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_32618, c_24])).
% 17.05/9.37  tff(c_32737, plain, (k1_xboole_0='#skF_4' | u1_struct_0('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32620, c_32711])).
% 17.05/9.37  tff(c_32746, plain, (u1_struct_0('#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_32737])).
% 17.05/9.37  tff(c_32754, plain, (v4_relat_1('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32746, c_144])).
% 17.05/9.37  tff(c_32756, plain, $false, inference(negUnitSimplification, [status(thm)], [c_27416, c_32754])).
% 17.05/9.37  tff(c_32757, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_32737])).
% 17.05/9.37  tff(c_32768, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32757, c_32620])).
% 17.05/9.37  tff(c_32759, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_32757, c_32618])).
% 17.05/9.37  tff(c_27257, plain, (![B_1408]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_1408, u1_struct_0('#skF_2')))) | ~r1_tarski(k1_relat_1('#skF_4'), B_1408))), inference(resolution, [status(thm)], [c_91, c_27251])).
% 17.05/9.37  tff(c_32612, plain, (![B_1408]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_1408, k1_xboole_0))) | ~r1_tarski(k1_relat_1('#skF_4'), B_1408))), inference(demodulation, [status(thm), theory('equality')], [c_32605, c_27257])).
% 17.05/9.37  tff(c_32929, plain, (![B_1408]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_1408, '#skF_4'))) | ~r1_tarski(k1_relat_1('#skF_4'), B_1408))), inference(demodulation, [status(thm), theory('equality')], [c_32757, c_32612])).
% 17.05/9.37  tff(c_33033, plain, (![A_1794]: (v1_funct_2('#skF_4', A_1794, '#skF_4') | A_1794='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_1794, '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_32757, c_32757, c_32757, c_32757, c_32757, c_22])).
% 17.05/9.37  tff(c_33044, plain, (![B_1795]: (v1_funct_2('#skF_4', B_1795, '#skF_4') | B_1795='#skF_4' | ~r1_tarski(k1_relat_1('#skF_4'), B_1795))), inference(resolution, [status(thm)], [c_32929, c_33033])).
% 17.05/9.37  tff(c_33056, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_4') | k1_relat_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_6, c_33044])).
% 17.05/9.37  tff(c_33057, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(splitLeft, [status(thm)], [c_33056])).
% 17.05/9.37  tff(c_32774, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32757, c_27410])).
% 17.05/9.37  tff(c_33066, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_33057, c_32774])).
% 17.05/9.37  tff(c_33073, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_33066])).
% 17.05/9.37  tff(c_33074, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_33056])).
% 17.05/9.37  tff(c_32614, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_32605, c_27218])).
% 17.05/9.37  tff(c_32985, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_32757, c_32614])).
% 17.05/9.37  tff(c_32771, plain, (u1_struct_0('#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_32757, c_32605])).
% 17.05/9.37  tff(c_32819, plain, (k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))), '#skF_4')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32771, c_27228])).
% 17.05/9.37  tff(c_27427, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0 | k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')=u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(resolution, [status(thm)], [c_60, c_27418])).
% 17.05/9.37  tff(c_27435, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0 | k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')=u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_27427])).
% 17.05/9.37  tff(c_33076, plain, (u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))='#skF_4' | u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32819, c_32771, c_32757, c_32771, c_27435])).
% 17.05/9.37  tff(c_33077, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_33076])).
% 17.05/9.37  tff(c_33126, plain, (v1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_33077, c_149])).
% 17.05/9.37  tff(c_33276, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_33126])).
% 17.05/9.37  tff(c_33299, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_120, c_33276])).
% 17.05/9.37  tff(c_33303, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_33299])).
% 17.05/9.37  tff(c_33305, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_33126])).
% 17.05/9.37  tff(c_33123, plain, (v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_33077, c_46])).
% 17.05/9.37  tff(c_33369, plain, (v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_33305, c_33123])).
% 17.05/9.37  tff(c_33370, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_33369])).
% 17.05/9.37  tff(c_33373, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_33370])).
% 17.05/9.37  tff(c_33377, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_33373])).
% 17.05/9.37  tff(c_33379, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_33369])).
% 17.05/9.37  tff(c_32619, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_32605, c_62])).
% 17.05/9.37  tff(c_32770, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_32757, c_32619])).
% 17.05/9.37  tff(c_33079, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_33077, c_32770])).
% 17.05/9.37  tff(c_32609, plain, (![B_1408]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_1408, u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2')))))) | ~r1_tarski(k1_relat_1('#skF_4'), B_1408))), inference(demodulation, [status(thm), theory('equality')], [c_32605, c_27256])).
% 17.05/9.37  tff(c_32990, plain, (![B_1408]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_1408, u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))))) | ~r1_tarski(k1_relat_1('#skF_4'), B_1408))), inference(demodulation, [status(thm), theory('equality')], [c_32757, c_32609])).
% 17.05/9.37  tff(c_32974, plain, (![D_1790, A_1791, B_1792]: (v5_pre_topc(D_1790, A_1791, g1_pre_topc(u1_struct_0(B_1792), u1_pre_topc(B_1792))) | ~v5_pre_topc(D_1790, A_1791, B_1792) | ~m1_subset_1(D_1790, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1791), u1_struct_0(g1_pre_topc(u1_struct_0(B_1792), u1_pre_topc(B_1792)))))) | ~v1_funct_2(D_1790, u1_struct_0(A_1791), u1_struct_0(g1_pre_topc(u1_struct_0(B_1792), u1_pre_topc(B_1792)))) | ~m1_subset_1(D_1790, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1791), u1_struct_0(B_1792)))) | ~v1_funct_2(D_1790, u1_struct_0(A_1791), u1_struct_0(B_1792)) | ~v1_funct_1(D_1790) | ~l1_pre_topc(B_1792) | ~v2_pre_topc(B_1792) | ~l1_pre_topc(A_1791) | ~v2_pre_topc(A_1791))), inference(cnfTransformation, [status(thm)], [f_163])).
% 17.05/9.37  tff(c_32980, plain, (![D_1790, A_1791]: (v5_pre_topc(D_1790, A_1791, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc(D_1790, A_1791, '#skF_2') | ~m1_subset_1(D_1790, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1791), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))))) | ~v1_funct_2(D_1790, u1_struct_0(A_1791), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1(D_1790, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1791), u1_struct_0('#skF_2')))) | ~v1_funct_2(D_1790, u1_struct_0(A_1791), u1_struct_0('#skF_2')) | ~v1_funct_1(D_1790) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(A_1791) | ~v2_pre_topc(A_1791))), inference(superposition, [status(thm), theory('equality')], [c_32771, c_32974])).
% 17.05/9.37  tff(c_34041, plain, (![D_1871, A_1872]: (v5_pre_topc(D_1871, A_1872, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc(D_1871, A_1872, '#skF_2') | ~m1_subset_1(D_1871, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1872), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))))) | ~v1_funct_2(D_1871, u1_struct_0(A_1872), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~m1_subset_1(D_1871, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1872), '#skF_4'))) | ~v1_funct_2(D_1871, u1_struct_0(A_1872), '#skF_4') | ~v1_funct_1(D_1871) | ~l1_pre_topc(A_1872) | ~v2_pre_topc(A_1872))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_32771, c_32771, c_32771, c_32771, c_32980])).
% 17.05/9.37  tff(c_34048, plain, (![A_1872]: (v5_pre_topc('#skF_4', A_1872, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', A_1872, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0(A_1872), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1872), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1872), '#skF_4') | ~v1_funct_1('#skF_4') | ~l1_pre_topc(A_1872) | ~v2_pre_topc(A_1872) | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(A_1872)))), inference(resolution, [status(thm)], [c_32990, c_34041])).
% 17.05/9.37  tff(c_34077, plain, (![A_1875]: (v5_pre_topc('#skF_4', A_1875, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', A_1875, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0(A_1875), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1875), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1875), '#skF_4') | ~l1_pre_topc(A_1875) | ~v2_pre_topc(A_1875) | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(A_1875)))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_34048])).
% 17.05/9.37  tff(c_34083, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_33077, c_34077])).
% 17.05/9.37  tff(c_34089, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_33077, c_33379, c_33305, c_33074, c_33077, c_33077, c_33079, c_34083])).
% 17.05/9.37  tff(c_34090, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_32985, c_34089])).
% 17.05/9.37  tff(c_34093, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_4')))), inference(splitLeft, [status(thm)], [c_34090])).
% 17.05/9.37  tff(c_34096, plain, (~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_32929, c_34093])).
% 17.05/9.37  tff(c_34100, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_34096])).
% 17.05/9.37  tff(c_34102, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_4')))), inference(splitRight, [status(thm)], [c_34090])).
% 17.05/9.37  tff(c_52, plain, (![D_42, A_28, B_36]: (v5_pre_topc(D_42, g1_pre_topc(u1_struct_0(A_28), u1_pre_topc(A_28)), B_36) | ~v5_pre_topc(D_42, A_28, B_36) | ~m1_subset_1(D_42, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_28), u1_pre_topc(A_28))), u1_struct_0(B_36)))) | ~v1_funct_2(D_42, u1_struct_0(g1_pre_topc(u1_struct_0(A_28), u1_pre_topc(A_28))), u1_struct_0(B_36)) | ~m1_subset_1(D_42, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_28), u1_struct_0(B_36)))) | ~v1_funct_2(D_42, u1_struct_0(A_28), u1_struct_0(B_36)) | ~v1_funct_1(D_42) | ~l1_pre_topc(B_36) | ~v2_pre_topc(B_36) | ~l1_pre_topc(A_28) | ~v2_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_134])).
% 17.05/9.37  tff(c_33117, plain, (![D_42, B_36]: (v5_pre_topc(D_42, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_36) | ~v5_pre_topc(D_42, '#skF_1', B_36) | ~m1_subset_1(D_42, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_36)))) | ~v1_funct_2(D_42, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_36)) | ~m1_subset_1(D_42, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_36)))) | ~v1_funct_2(D_42, u1_struct_0('#skF_1'), u1_struct_0(B_36)) | ~v1_funct_1(D_42) | ~l1_pre_topc(B_36) | ~v2_pre_topc(B_36) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_33077, c_52])).
% 17.05/9.37  tff(c_33979, plain, (![D_1866, B_1867]: (v5_pre_topc(D_1866, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_1867) | ~v5_pre_topc(D_1866, '#skF_1', B_1867) | ~m1_subset_1(D_1866, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_1867)))) | ~v1_funct_2(D_1866, k1_relat_1('#skF_4'), u1_struct_0(B_1867)) | ~m1_subset_1(D_1866, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_1867)))) | ~v1_funct_2(D_1866, u1_struct_0('#skF_1'), u1_struct_0(B_1867)) | ~v1_funct_1(D_1866) | ~l1_pre_topc(B_1867) | ~v2_pre_topc(B_1867))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_33077, c_33117])).
% 17.05/9.37  tff(c_33989, plain, (![D_1866]: (v5_pre_topc(D_1866, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~v5_pre_topc(D_1866, '#skF_1', '#skF_2') | ~m1_subset_1(D_1866, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(D_1866, k1_relat_1('#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(D_1866, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), '#skF_4'))) | ~v1_funct_2(D_1866, u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(D_1866) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_32771, c_33979])).
% 17.05/9.37  tff(c_33997, plain, (![D_1866]: (v5_pre_topc(D_1866, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~v5_pre_topc(D_1866, '#skF_1', '#skF_2') | ~m1_subset_1(D_1866, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_4'))) | ~v1_funct_2(D_1866, k1_relat_1('#skF_4'), '#skF_4') | ~m1_subset_1(D_1866, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), '#skF_4'))) | ~v1_funct_2(D_1866, u1_struct_0('#skF_1'), '#skF_4') | ~v1_funct_1(D_1866))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_32771, c_32771, c_32771, c_33989])).
% 17.05/9.37  tff(c_34101, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')), inference(splitRight, [status(thm)], [c_34090])).
% 17.05/9.37  tff(c_34169, plain, (~v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_4'))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_33997, c_34101])).
% 17.05/9.37  tff(c_34173, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_32768, c_32759, c_33074, c_34102, c_27217, c_34169])).
% 17.05/9.37  tff(c_34174, plain, (u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))='#skF_4'), inference(splitRight, [status(thm)], [c_33076])).
% 17.05/9.37  tff(c_34177, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34174, c_32770])).
% 17.05/9.37  tff(c_32984, plain, (![D_1790, A_1791]: (v5_pre_topc(D_1790, A_1791, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc(D_1790, A_1791, '#skF_2') | ~m1_subset_1(D_1790, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1791), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))))) | ~v1_funct_2(D_1790, u1_struct_0(A_1791), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~m1_subset_1(D_1790, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1791), '#skF_4'))) | ~v1_funct_2(D_1790, u1_struct_0(A_1791), '#skF_4') | ~v1_funct_1(D_1790) | ~l1_pre_topc(A_1791) | ~v2_pre_topc(A_1791))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_32771, c_32771, c_32771, c_32771, c_32980])).
% 17.05/9.37  tff(c_34416, plain, (![D_1897, A_1898]: (v5_pre_topc(D_1897, A_1898, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc(D_1897, A_1898, '#skF_2') | ~m1_subset_1(D_1897, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1898), '#skF_4'))) | ~v1_funct_2(D_1897, u1_struct_0(A_1898), '#skF_4') | ~m1_subset_1(D_1897, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1898), '#skF_4'))) | ~v1_funct_2(D_1897, u1_struct_0(A_1898), '#skF_4') | ~v1_funct_1(D_1897) | ~l1_pre_topc(A_1898) | ~v2_pre_topc(A_1898))), inference(demodulation, [status(thm), theory('equality')], [c_34174, c_34174, c_32984])).
% 17.05/9.37  tff(c_34425, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4') | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32759, c_34416])).
% 17.05/9.37  tff(c_34439, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_64, c_32768, c_32759, c_27217, c_34425])).
% 17.05/9.37  tff(c_32624, plain, (v2_pre_topc(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_32605, c_46])).
% 17.05/9.37  tff(c_32637, plain, (v2_pre_topc(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_32624])).
% 17.05/9.37  tff(c_32767, plain, (v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_32757, c_32637])).
% 17.05/9.37  tff(c_32630, plain, (l1_pre_topc(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_32605, c_120])).
% 17.05/9.37  tff(c_32641, plain, (l1_pre_topc(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_32630])).
% 17.05/9.37  tff(c_32766, plain, (l1_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_32757, c_32641])).
% 17.05/9.37  tff(c_32991, plain, (![B_1793]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_1793, u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))))) | ~r1_tarski(k1_relat_1('#skF_4'), B_1793))), inference(demodulation, [status(thm), theory('equality')], [c_32757, c_32609])).
% 17.05/9.37  tff(c_32999, plain, (![A_28]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_28), u1_pre_topc(A_28)), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', A_28, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_28), u1_pre_topc(A_28))), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_28), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))))) | ~v1_funct_2('#skF_4', u1_struct_0(A_28), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_28) | ~v2_pre_topc(A_28) | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0(A_28), u1_pre_topc(A_28)))))), inference(resolution, [status(thm)], [c_32991, c_52])).
% 17.05/9.37  tff(c_33022, plain, (![A_28]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_28), u1_pre_topc(A_28)), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', A_28, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_28), u1_pre_topc(A_28))), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_28), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))))) | ~v1_funct_2('#skF_4', u1_struct_0(A_28), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~l1_pre_topc(A_28) | ~v2_pre_topc(A_28) | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0(A_28), u1_pre_topc(A_28)))))), inference(demodulation, [status(thm), theory('equality')], [c_32767, c_32766, c_64, c_32999])).
% 17.05/9.37  tff(c_34658, plain, (![A_1915]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_1915), u1_pre_topc(A_1915)), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', A_1915, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_1915), u1_pre_topc(A_1915))), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1915), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1915), '#skF_4') | ~l1_pre_topc(A_1915) | ~v2_pre_topc(A_1915) | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0(A_1915), u1_pre_topc(A_1915)))))), inference(demodulation, [status(thm), theory('equality')], [c_34174, c_34174, c_34174, c_33022])).
% 17.05/9.37  tff(c_34667, plain, (~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(resolution, [status(thm)], [c_34658, c_32985])).
% 17.05/9.37  tff(c_34678, plain, (~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_32768, c_32759, c_34177, c_34439, c_34667])).
% 17.05/9.37  tff(c_34685, plain, (~v4_relat_1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_34678])).
% 17.05/9.37  tff(c_34689, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_110, c_143, c_34685])).
% 17.05/9.37  tff(c_34691, plain, (r1_tarski(k1_relat_1('#skF_4'), k1_xboole_0)), inference(splitRight, [status(thm)], [c_27282])).
% 17.05/9.37  tff(c_27284, plain, (![B_1411]: (k1_relset_1(B_1411, u1_struct_0('#skF_2'), '#skF_4')=k1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), B_1411))), inference(resolution, [status(thm)], [c_27258, c_18])).
% 17.05/9.37  tff(c_34703, plain, (k1_relset_1(k1_xboole_0, u1_struct_0('#skF_2'), '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34691, c_27284])).
% 17.05/9.37  tff(c_27303, plain, (![C_1413, A_1414, B_1415]: (v1_funct_2(C_1413, A_1414, B_1415) | k1_relset_1(A_1414, B_1415, C_1413)!=A_1414 | ~m1_subset_1(C_1413, k1_zfmisc_1(k2_zfmisc_1(A_1414, B_1415))) | ~v1_funct_1(C_1413))), inference(cnfTransformation, [status(thm)], [f_87])).
% 17.05/9.37  tff(c_27306, plain, (![B_1408]: (v1_funct_2('#skF_4', B_1408, u1_struct_0('#skF_2')) | k1_relset_1(B_1408, u1_struct_0('#skF_2'), '#skF_4')!=B_1408 | ~v1_funct_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), B_1408))), inference(resolution, [status(thm)], [c_27257, c_27303])).
% 17.05/9.37  tff(c_34850, plain, (![B_1922]: (v1_funct_2('#skF_4', B_1922, u1_struct_0('#skF_2')) | k1_relset_1(B_1922, u1_struct_0('#skF_2'), '#skF_4')!=B_1922 | ~r1_tarski(k1_relat_1('#skF_4'), B_1922))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_27306])).
% 17.05/9.37  tff(c_34690, plain, (~v1_funct_2('#skF_4', k1_xboole_0, u1_struct_0('#skF_2')) | k1_relset_1(k1_xboole_0, u1_struct_0('#skF_2'), '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_27282])).
% 17.05/9.37  tff(c_34848, plain, (~v1_funct_2('#skF_4', k1_xboole_0, u1_struct_0('#skF_2')) | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34703, c_34690])).
% 17.05/9.37  tff(c_34849, plain, (~v1_funct_2('#skF_4', k1_xboole_0, u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_34848])).
% 17.05/9.37  tff(c_34853, plain, (k1_relset_1(k1_xboole_0, u1_struct_0('#skF_2'), '#skF_4')!=k1_xboole_0 | ~r1_tarski(k1_relat_1('#skF_4'), k1_xboole_0)), inference(resolution, [status(thm)], [c_34850, c_34849])).
% 17.05/9.37  tff(c_34856, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34691, c_34703, c_34853])).
% 17.05/9.37  tff(c_34726, plain, (![B_1916, A_1917, C_1918]: (k1_xboole_0=B_1916 | k1_relset_1(A_1917, B_1916, C_1918)=A_1917 | ~v1_funct_2(C_1918, A_1917, B_1916) | ~m1_subset_1(C_1918, k1_zfmisc_1(k2_zfmisc_1(A_1917, B_1916))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 17.05/9.37  tff(c_34738, plain, (u1_struct_0('#skF_2')=k1_xboole_0 | k1_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4')=u1_struct_0('#skF_1') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_91, c_34726])).
% 17.05/9.37  tff(c_34746, plain, (u1_struct_0('#skF_2')=k1_xboole_0 | u1_struct_0('#skF_1')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_87, c_27229, c_34738])).
% 17.05/9.37  tff(c_34747, plain, (u1_struct_0('#skF_1')=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_34746])).
% 17.05/9.37  tff(c_34749, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_34747, c_27218])).
% 17.05/9.37  tff(c_34754, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_34747, c_62])).
% 17.05/9.37  tff(c_34843, plain, (k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34747, c_27228])).
% 17.05/9.37  tff(c_34752, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))))), inference(demodulation, [status(thm), theory('equality')], [c_34747, c_60])).
% 17.05/9.37  tff(c_34907, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0 | k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')=u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(resolution, [status(thm)], [c_34752, c_32])).
% 17.05/9.37  tff(c_34929, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0 | u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34754, c_34843, c_34907])).
% 17.05/9.37  tff(c_34945, plain, (u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_34929])).
% 17.05/9.37  tff(c_34761, plain, (v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_34747, c_46])).
% 17.05/9.37  tff(c_34774, plain, (v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_34761])).
% 17.05/9.37  tff(c_34767, plain, (l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_34747, c_120])).
% 17.05/9.37  tff(c_34778, plain, (l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_34767])).
% 17.05/9.37  tff(c_34755, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34747, c_87])).
% 17.05/9.37  tff(c_34753, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_34747, c_91])).
% 17.05/9.37  tff(c_34949, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_34945, c_34754])).
% 17.05/9.37  tff(c_37435, plain, (![D_2051, A_2052, B_2053]: (v5_pre_topc(D_2051, g1_pre_topc(u1_struct_0(A_2052), u1_pre_topc(A_2052)), B_2053) | ~v5_pre_topc(D_2051, A_2052, B_2053) | ~m1_subset_1(D_2051, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2052), u1_pre_topc(A_2052))), u1_struct_0(B_2053)))) | ~v1_funct_2(D_2051, u1_struct_0(g1_pre_topc(u1_struct_0(A_2052), u1_pre_topc(A_2052))), u1_struct_0(B_2053)) | ~m1_subset_1(D_2051, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2052), u1_struct_0(B_2053)))) | ~v1_funct_2(D_2051, u1_struct_0(A_2052), u1_struct_0(B_2053)) | ~v1_funct_1(D_2051) | ~l1_pre_topc(B_2053) | ~v2_pre_topc(B_2053) | ~l1_pre_topc(A_2052) | ~v2_pre_topc(A_2052))), inference(cnfTransformation, [status(thm)], [f_134])).
% 17.05/9.37  tff(c_37444, plain, (![D_2051, B_2053]: (v5_pre_topc(D_2051, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_2053) | ~v5_pre_topc(D_2051, '#skF_1', B_2053) | ~m1_subset_1(D_2051, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(B_2053)))) | ~v1_funct_2(D_2051, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_2053)) | ~m1_subset_1(D_2051, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_2053)))) | ~v1_funct_2(D_2051, u1_struct_0('#skF_1'), u1_struct_0(B_2053)) | ~v1_funct_1(D_2051) | ~l1_pre_topc(B_2053) | ~v2_pre_topc(B_2053) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_34747, c_37435])).
% 17.05/9.37  tff(c_37471, plain, (![D_2055, B_2056]: (v5_pre_topc(D_2055, g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), B_2056) | ~v5_pre_topc(D_2055, '#skF_1', B_2056) | ~m1_subset_1(D_2055, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_2056)))) | ~v1_funct_2(D_2055, k1_relat_1('#skF_4'), u1_struct_0(B_2056)) | ~v1_funct_1(D_2055) | ~l1_pre_topc(B_2056) | ~v2_pre_topc(B_2056))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_34747, c_34747, c_34945, c_34747, c_34945, c_34747, c_37444])).
% 17.05/9.37  tff(c_37480, plain, (v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), '#skF_2') | ~v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_34753, c_37471])).
% 17.05/9.37  tff(c_37500, plain, (v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_64, c_34755, c_27217, c_37480])).
% 17.05/9.37  tff(c_34985, plain, (![D_1927, A_1928, B_1929]: (v5_pre_topc(D_1927, A_1928, g1_pre_topc(u1_struct_0(B_1929), u1_pre_topc(B_1929))) | ~v5_pre_topc(D_1927, A_1928, B_1929) | ~m1_subset_1(D_1927, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1928), u1_struct_0(g1_pre_topc(u1_struct_0(B_1929), u1_pre_topc(B_1929)))))) | ~v1_funct_2(D_1927, u1_struct_0(A_1928), u1_struct_0(g1_pre_topc(u1_struct_0(B_1929), u1_pre_topc(B_1929)))) | ~m1_subset_1(D_1927, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1928), u1_struct_0(B_1929)))) | ~v1_funct_2(D_1927, u1_struct_0(A_1928), u1_struct_0(B_1929)) | ~v1_funct_1(D_1927) | ~l1_pre_topc(B_1929) | ~v2_pre_topc(B_1929) | ~l1_pre_topc(A_1928) | ~v2_pre_topc(A_1928))), inference(cnfTransformation, [status(thm)], [f_163])).
% 17.05/9.37  tff(c_35001, plain, (![A_1928]: (v5_pre_topc('#skF_4', A_1928, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', A_1928, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0(A_1928), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1928), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1928), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(A_1928) | ~v2_pre_topc(A_1928) | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(A_1928)))), inference(resolution, [status(thm)], [c_27256, c_34985])).
% 17.05/9.37  tff(c_37510, plain, (![A_2057]: (v5_pre_topc('#skF_4', A_2057, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', A_2057, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0(A_2057), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2057), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0(A_2057), u1_struct_0('#skF_2')) | ~l1_pre_topc(A_2057) | ~v2_pre_topc(A_2057) | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(A_2057)))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_64, c_35001])).
% 17.05/9.37  tff(c_37516, plain, (v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), '#skF_2') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0('#skF_2')) | ~l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))) | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_34945, c_37510])).
% 17.05/9.37  tff(c_37522, plain, (v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_34945, c_34774, c_34778, c_34755, c_34945, c_34753, c_34945, c_34949, c_37500, c_37516])).
% 17.05/9.37  tff(c_37524, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34749, c_37522])).
% 17.05/9.37  tff(c_37525, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0), inference(splitRight, [status(thm)], [c_34929])).
% 17.05/9.37  tff(c_27339, plain, (![B_1417]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_1417, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))))) | ~r1_tarski(k1_relat_1('#skF_4'), B_1417))), inference(resolution, [status(thm)], [c_60, c_27251])).
% 17.05/9.37  tff(c_27369, plain, (k1_relset_1(k1_xboole_0, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_4', k1_xboole_0, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~r1_tarski(k1_relat_1('#skF_4'), k1_xboole_0)), inference(resolution, [status(thm)], [c_27339, c_30])).
% 17.05/9.37  tff(c_34943, plain, (k1_relset_1(k1_xboole_0, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_4', k1_xboole_0, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_34691, c_27369])).
% 17.05/9.37  tff(c_34944, plain, (~v1_funct_2('#skF_4', k1_xboole_0, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(splitLeft, [status(thm)], [c_34943])).
% 17.05/9.37  tff(c_37527, plain, (~v1_funct_2('#skF_4', k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_37525, c_34944])).
% 17.05/9.37  tff(c_37531, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_37525, c_34754])).
% 17.05/9.37  tff(c_37528, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_37525, c_34752])).
% 17.05/9.37  tff(c_37712, plain, (k1_xboole_0='#skF_4' | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), k1_xboole_0) | u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))=k1_xboole_0), inference(resolution, [status(thm)], [c_37528, c_24])).
% 17.05/9.37  tff(c_37738, plain, (k1_xboole_0='#skF_4' | u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_37531, c_37712])).
% 17.05/9.37  tff(c_37746, plain, (u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))=k1_xboole_0), inference(splitLeft, [status(thm)], [c_37738])).
% 17.05/9.37  tff(c_37748, plain, (v1_funct_2('#skF_4', k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_37746, c_37531])).
% 17.05/9.37  tff(c_37752, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37527, c_37748])).
% 17.05/9.37  tff(c_37753, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_37738])).
% 17.05/9.37  tff(c_27371, plain, (![B_1417]: (k1_relset_1(B_1417, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')=k1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), B_1417))), inference(resolution, [status(thm)], [c_27339, c_18])).
% 17.05/9.37  tff(c_37594, plain, (![B_2061]: (k1_relset_1(B_2061, k1_xboole_0, '#skF_4')=k1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), B_2061))), inference(demodulation, [status(thm), theory('equality')], [c_37525, c_27371])).
% 17.05/9.37  tff(c_37610, plain, (k1_relset_1(k1_relat_1('#skF_4'), k1_xboole_0, '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_6, c_37594])).
% 17.05/9.37  tff(c_37758, plain, (k1_relset_1(k1_relat_1('#skF_4'), '#skF_4', '#skF_4')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_37753, c_37610])).
% 17.05/9.37  tff(c_37526, plain, (u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))!=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_34929])).
% 17.05/9.37  tff(c_37530, plain, (k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), k1_xboole_0, '#skF_4')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_37525, c_34843])).
% 17.05/9.37  tff(c_37942, plain, (k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), '#skF_4', '#skF_4')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_37753, c_37530])).
% 17.05/9.37  tff(c_37764, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_37753, c_37525])).
% 17.05/9.37  tff(c_34735, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0 | k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')=u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(resolution, [status(thm)], [c_60, c_34726])).
% 17.05/9.37  tff(c_34743, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0 | k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')=u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_34735])).
% 17.05/9.37  tff(c_37845, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))='#skF_4' | k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')=u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34747, c_34747, c_37753, c_34743])).
% 17.05/9.37  tff(c_37846, plain, (k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')=u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_37845])).
% 17.05/9.37  tff(c_38681, plain, (u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_37942, c_37764, c_37846])).
% 17.05/9.37  tff(c_38682, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37526, c_38681])).
% 17.05/9.37  tff(c_38683, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))='#skF_4'), inference(splitRight, [status(thm)], [c_37845])).
% 17.05/9.37  tff(c_36, plain, (![C_23, A_21, B_22]: (v1_funct_2(C_23, A_21, B_22) | k1_relset_1(A_21, B_22, C_23)!=A_21 | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))) | ~v1_funct_1(C_23))), inference(cnfTransformation, [status(thm)], [f_87])).
% 17.05/9.37  tff(c_27342, plain, (![B_1417]: (v1_funct_2('#skF_4', B_1417, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | k1_relset_1(B_1417, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')!=B_1417 | ~v1_funct_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), B_1417))), inference(resolution, [status(thm)], [c_27339, c_36])).
% 17.05/9.37  tff(c_27367, plain, (![B_1417]: (v1_funct_2('#skF_4', B_1417, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | k1_relset_1(B_1417, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')!=B_1417 | ~r1_tarski(k1_relat_1('#skF_4'), B_1417))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_27342])).
% 17.05/9.37  tff(c_39633, plain, (![B_2163]: (v1_funct_2('#skF_4', B_2163, '#skF_4') | k1_relset_1(B_2163, '#skF_4', '#skF_4')!=B_2163 | ~r1_tarski(k1_relat_1('#skF_4'), B_2163))), inference(demodulation, [status(thm), theory('equality')], [c_38683, c_38683, c_27367])).
% 17.05/9.37  tff(c_39644, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_4') | k1_relset_1(k1_relat_1('#skF_4'), '#skF_4', '#skF_4')!=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_6, c_39633])).
% 17.05/9.37  tff(c_39653, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_37758, c_39644])).
% 17.05/9.37  tff(c_37532, plain, (![B_1408]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_1408, k1_xboole_0))) | ~r1_tarski(k1_relat_1('#skF_4'), B_1408))), inference(demodulation, [status(thm), theory('equality')], [c_37525, c_27256])).
% 17.05/9.37  tff(c_37757, plain, (![B_1408]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_1408, '#skF_4'))) | ~r1_tarski(k1_relat_1('#skF_4'), B_1408))), inference(demodulation, [status(thm), theory('equality')], [c_37753, c_37532])).
% 17.05/9.37  tff(c_56, plain, (![D_57, A_43, B_51]: (v5_pre_topc(D_57, A_43, g1_pre_topc(u1_struct_0(B_51), u1_pre_topc(B_51))) | ~v5_pre_topc(D_57, A_43, B_51) | ~m1_subset_1(D_57, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_43), u1_struct_0(g1_pre_topc(u1_struct_0(B_51), u1_pre_topc(B_51)))))) | ~v1_funct_2(D_57, u1_struct_0(A_43), u1_struct_0(g1_pre_topc(u1_struct_0(B_51), u1_pre_topc(B_51)))) | ~m1_subset_1(D_57, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_43), u1_struct_0(B_51)))) | ~v1_funct_2(D_57, u1_struct_0(A_43), u1_struct_0(B_51)) | ~v1_funct_1(D_57) | ~l1_pre_topc(B_51) | ~v2_pre_topc(B_51) | ~l1_pre_topc(A_43) | ~v2_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_163])).
% 17.05/9.37  tff(c_38704, plain, (![D_57, A_43]: (v5_pre_topc(D_57, A_43, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc(D_57, A_43, '#skF_2') | ~m1_subset_1(D_57, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_43), '#skF_4'))) | ~v1_funct_2(D_57, u1_struct_0(A_43), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1(D_57, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_43), u1_struct_0('#skF_2')))) | ~v1_funct_2(D_57, u1_struct_0(A_43), u1_struct_0('#skF_2')) | ~v1_funct_1(D_57) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(A_43) | ~v2_pre_topc(A_43))), inference(superposition, [status(thm), theory('equality')], [c_38683, c_56])).
% 17.05/9.37  tff(c_40034, plain, (![D_2194, A_2195]: (v5_pre_topc(D_2194, A_2195, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc(D_2194, A_2195, '#skF_2') | ~m1_subset_1(D_2194, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2195), '#skF_4'))) | ~v1_funct_2(D_2194, u1_struct_0(A_2195), '#skF_4') | ~m1_subset_1(D_2194, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2195), u1_struct_0('#skF_2')))) | ~v1_funct_2(D_2194, u1_struct_0(A_2195), u1_struct_0('#skF_2')) | ~v1_funct_1(D_2194) | ~l1_pre_topc(A_2195) | ~v2_pre_topc(A_2195))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_38683, c_38704])).
% 17.05/9.37  tff(c_40040, plain, (![D_2194]: (v5_pre_topc(D_2194, '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc(D_2194, '#skF_1', '#skF_2') | ~m1_subset_1(D_2194, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), '#skF_4'))) | ~v1_funct_2(D_2194, u1_struct_0('#skF_1'), '#skF_4') | ~m1_subset_1(D_2194, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(D_2194, u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(D_2194) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_34747, c_40034])).
% 17.05/9.37  tff(c_40085, plain, (![D_2198]: (v5_pre_topc(D_2198, '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc(D_2198, '#skF_1', '#skF_2') | ~m1_subset_1(D_2198, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_4'))) | ~v1_funct_2(D_2198, k1_relat_1('#skF_4'), '#skF_4') | ~m1_subset_1(D_2198, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(D_2198, k1_relat_1('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(D_2198))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_34747, c_34747, c_34747, c_40040])).
% 17.05/9.37  tff(c_40088, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_4'))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_4') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_34753, c_40085])).
% 17.05/9.37  tff(c_40095, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_34755, c_39653, c_27217, c_40088])).
% 17.05/9.37  tff(c_40099, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_4')))), inference(splitLeft, [status(thm)], [c_40095])).
% 17.05/9.37  tff(c_40102, plain, (~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_37757, c_40099])).
% 17.05/9.37  tff(c_40106, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_40102])).
% 17.05/9.37  tff(c_40108, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_4')))), inference(splitRight, [status(thm)], [c_40095])).
% 17.05/9.37  tff(c_37761, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_37753, c_37531])).
% 17.05/9.37  tff(c_37755, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_37753, c_37528])).
% 17.05/9.37  tff(c_40107, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_40095])).
% 17.05/9.37  tff(c_37549, plain, (v1_pre_topc(g1_pre_topc(k1_xboole_0, u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_37525, c_149])).
% 17.05/9.37  tff(c_39704, plain, (v1_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_37753, c_37549])).
% 17.05/9.37  tff(c_39705, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_39704])).
% 17.05/9.37  tff(c_39710, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_120, c_39705])).
% 17.05/9.37  tff(c_39714, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_39710])).
% 17.05/9.37  tff(c_39716, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_39704])).
% 17.05/9.37  tff(c_34857, plain, (![D_1923, A_1924, B_1925]: (v5_pre_topc(D_1923, A_1924, B_1925) | ~v5_pre_topc(D_1923, g1_pre_topc(u1_struct_0(A_1924), u1_pre_topc(A_1924)), B_1925) | ~m1_subset_1(D_1923, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1924), u1_pre_topc(A_1924))), u1_struct_0(B_1925)))) | ~v1_funct_2(D_1923, u1_struct_0(g1_pre_topc(u1_struct_0(A_1924), u1_pre_topc(A_1924))), u1_struct_0(B_1925)) | ~m1_subset_1(D_1923, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1924), u1_struct_0(B_1925)))) | ~v1_funct_2(D_1923, u1_struct_0(A_1924), u1_struct_0(B_1925)) | ~v1_funct_1(D_1923) | ~l1_pre_topc(B_1925) | ~v2_pre_topc(B_1925) | ~l1_pre_topc(A_1924) | ~v2_pre_topc(A_1924))), inference(cnfTransformation, [status(thm)], [f_134])).
% 17.05/9.37  tff(c_34867, plain, (![A_1924]: (v5_pre_topc('#skF_4', A_1924, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_1924), u1_pre_topc(A_1924)), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_1924), u1_pre_topc(A_1924))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1924), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1924), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_1924) | ~v2_pre_topc(A_1924) | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0(A_1924), u1_pre_topc(A_1924)))))), inference(resolution, [status(thm)], [c_27256, c_34857])).
% 17.05/9.37  tff(c_34878, plain, (![A_1924]: (v5_pre_topc('#skF_4', A_1924, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_1924), u1_pre_topc(A_1924)), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_1924), u1_pre_topc(A_1924))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1924), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1924), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_1924) | ~v2_pre_topc(A_1924) | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0(A_1924), u1_pre_topc(A_1924)))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_34867])).
% 17.05/9.37  tff(c_39787, plain, (![A_1924]: (v5_pre_topc('#skF_4', A_1924, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_1924), u1_pre_topc(A_1924)), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_1924), u1_pre_topc(A_1924))), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1924), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1924), '#skF_4') | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_1924) | ~v2_pre_topc(A_1924) | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0(A_1924), u1_pre_topc(A_1924)))))), inference(demodulation, [status(thm), theory('equality')], [c_39716, c_38683, c_38683, c_38683, c_34878])).
% 17.05/9.37  tff(c_39788, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_39787])).
% 17.05/9.37  tff(c_39791, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_46, c_39788])).
% 17.05/9.37  tff(c_39795, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_39791])).
% 17.05/9.37  tff(c_39797, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_39787])).
% 17.05/9.37  tff(c_37563, plain, (![D_2058, A_2059, B_2060]: (v5_pre_topc(D_2058, g1_pre_topc(u1_struct_0(A_2059), u1_pre_topc(A_2059)), B_2060) | ~v5_pre_topc(D_2058, A_2059, B_2060) | ~m1_subset_1(D_2058, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2059), u1_pre_topc(A_2059))), u1_struct_0(B_2060)))) | ~v1_funct_2(D_2058, u1_struct_0(g1_pre_topc(u1_struct_0(A_2059), u1_pre_topc(A_2059))), u1_struct_0(B_2060)) | ~m1_subset_1(D_2058, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2059), u1_struct_0(B_2060)))) | ~v1_funct_2(D_2058, u1_struct_0(A_2059), u1_struct_0(B_2060)) | ~v1_funct_1(D_2058) | ~l1_pre_topc(B_2060) | ~v2_pre_topc(B_2060) | ~l1_pre_topc(A_2059) | ~v2_pre_topc(A_2059))), inference(cnfTransformation, [status(thm)], [f_134])).
% 17.05/9.37  tff(c_37575, plain, (![D_2058, B_2060]: (v5_pre_topc(D_2058, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_2060) | ~v5_pre_topc(D_2058, '#skF_1', B_2060) | ~m1_subset_1(D_2058, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(B_2060)))) | ~v1_funct_2(D_2058, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_2060)) | ~m1_subset_1(D_2058, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_2060)))) | ~v1_funct_2(D_2058, u1_struct_0('#skF_1'), u1_struct_0(B_2060)) | ~v1_funct_1(D_2058) | ~l1_pre_topc(B_2060) | ~v2_pre_topc(B_2060) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_34747, c_37563])).
% 17.05/9.37  tff(c_40295, plain, (![D_2209, B_2210]: (v5_pre_topc(D_2209, g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), B_2210) | ~v5_pre_topc(D_2209, '#skF_1', B_2210) | ~m1_subset_1(D_2209, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(B_2210)))) | ~v1_funct_2(D_2209, u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(B_2210)) | ~m1_subset_1(D_2209, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_2210)))) | ~v1_funct_2(D_2209, k1_relat_1('#skF_4'), u1_struct_0(B_2210)) | ~v1_funct_1(D_2209) | ~l1_pre_topc(B_2210) | ~v2_pre_topc(B_2210))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_34747, c_34747, c_34747, c_34747, c_37575])).
% 17.05/9.37  tff(c_40298, plain, (![D_2209]: (v5_pre_topc(D_2209, g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc(D_2209, '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_subset_1(D_2209, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), '#skF_4'))) | ~v1_funct_2(D_2209, u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1(D_2209, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))))) | ~v1_funct_2(D_2209, k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~v1_funct_1(D_2209) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_38683, c_40295])).
% 17.05/9.37  tff(c_40469, plain, (![D_2230]: (v5_pre_topc(D_2230, g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc(D_2230, '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_subset_1(D_2230, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), '#skF_4'))) | ~v1_funct_2(D_2230, u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), '#skF_4') | ~m1_subset_1(D_2230, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_4'))) | ~v1_funct_2(D_2230, k1_relat_1('#skF_4'), '#skF_4') | ~v1_funct_1(D_2230))), inference(demodulation, [status(thm), theory('equality')], [c_39797, c_39716, c_38683, c_38683, c_38683, c_40298])).
% 17.05/9.37  tff(c_40479, plain, (~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_4'))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_4') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_40469, c_34749])).
% 17.05/9.37  tff(c_40487, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_39653, c_40108, c_37761, c_37755, c_40107, c_40479])).
% 17.05/9.37  tff(c_40488, plain, (k1_relset_1(k1_xboole_0, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_34943])).
% 17.05/9.37  tff(c_40517, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | ~r1_tarski(k1_relat_1('#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_40488, c_27371])).
% 17.05/9.37  tff(c_40524, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34691, c_40517])).
% 17.05/9.37  tff(c_40526, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34856, c_40524])).
% 17.05/9.37  tff(c_40527, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_34848])).
% 17.05/9.37  tff(c_34708, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_34691, c_2])).
% 17.05/9.37  tff(c_34792, plain, (~r1_tarski(k1_xboole_0, k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_34708])).
% 17.05/9.37  tff(c_40532, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_40527, c_34792])).
% 17.05/9.37  tff(c_40551, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_40532])).
% 17.05/9.37  tff(c_40552, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_34708])).
% 17.05/9.37  tff(c_40929, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_40552, c_34749])).
% 17.05/9.37  tff(c_40566, plain, (u1_struct_0('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_40552, c_34747])).
% 17.05/9.37  tff(c_40554, plain, (k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34747, c_27228])).
% 17.05/9.37  tff(c_40559, plain, (k1_relset_1(u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_40552, c_40552, c_40554])).
% 17.05/9.37  tff(c_43961, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0 | u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1')))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_40566, c_40559, c_40566, c_34743])).
% 17.05/9.37  tff(c_43962, plain, (u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1')))=k1_xboole_0), inference(splitLeft, [status(thm)], [c_43961])).
% 17.05/9.37  tff(c_40629, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))))), inference(demodulation, [status(thm), theory('equality')], [c_40552, c_34752])).
% 17.05/9.37  tff(c_16, plain, (![C_10, A_8, B_9]: (v4_relat_1(C_10, A_8) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 17.05/9.37  tff(c_40662, plain, (v4_relat_1('#skF_4', u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1'))))), inference(resolution, [status(thm)], [c_40629, c_16])).
% 17.05/9.37  tff(c_40581, plain, (![A_78]: (k1_relat_1('#skF_4')=A_78 | ~r1_tarski(A_78, k1_xboole_0) | ~v4_relat_1('#skF_4', A_78) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_40552, c_115])).
% 17.05/9.37  tff(c_40777, plain, (![A_2242]: (k1_xboole_0=A_2242 | ~r1_tarski(A_2242, k1_xboole_0) | ~v4_relat_1('#skF_4', A_2242))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_40552, c_40581])).
% 17.05/9.37  tff(c_40791, plain, (u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1')))=k1_xboole_0 | ~r1_tarski(u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1'))), k1_xboole_0)), inference(resolution, [status(thm)], [c_40662, c_40777])).
% 17.05/9.37  tff(c_40930, plain, (~r1_tarski(u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1'))), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_40791])).
% 17.05/9.37  tff(c_43964, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_43962, c_40930])).
% 17.05/9.37  tff(c_43972, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_43964])).
% 17.05/9.37  tff(c_43974, plain, (u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1')))!=k1_xboole_0), inference(splitRight, [status(thm)], [c_43961])).
% 17.05/9.37  tff(c_43973, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0), inference(splitRight, [status(thm)], [c_43961])).
% 17.05/9.37  tff(c_40564, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_40552, c_34754])).
% 17.05/9.37  tff(c_43980, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1'))), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_43973, c_40564])).
% 17.05/9.37  tff(c_43981, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1'))), k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_43973, c_40629])).
% 17.05/9.37  tff(c_44144, plain, (k1_xboole_0='#skF_4' | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1'))), k1_xboole_0) | u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1')))=k1_xboole_0), inference(resolution, [status(thm)], [c_43981, c_24])).
% 17.05/9.37  tff(c_44171, plain, (k1_xboole_0='#skF_4' | u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1')))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_43980, c_44144])).
% 17.05/9.37  tff(c_44172, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_43974, c_44171])).
% 17.05/9.37  tff(c_44190, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_44172, c_43973])).
% 17.05/9.37  tff(c_40570, plain, (![B_1408]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_1408, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))))) | ~r1_tarski(k1_xboole_0, B_1408))), inference(demodulation, [status(thm), theory('equality')], [c_40552, c_27256])).
% 17.05/9.37  tff(c_43978, plain, (![B_1408]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_1408, k1_xboole_0))) | ~r1_tarski(k1_xboole_0, B_1408))), inference(demodulation, [status(thm), theory('equality')], [c_43973, c_40570])).
% 17.05/9.37  tff(c_44183, plain, (![B_1408]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_1408, '#skF_4'))) | ~r1_tarski('#skF_4', B_1408))), inference(demodulation, [status(thm), theory('equality')], [c_44172, c_44172, c_43978])).
% 17.05/9.37  tff(c_44197, plain, (~v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_44172, c_40929])).
% 17.05/9.37  tff(c_44203, plain, (v4_relat_1('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44172, c_40662])).
% 17.05/9.37  tff(c_40590, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3) | ~v4_relat_1('#skF_4', A_3) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_40552, c_10])).
% 17.05/9.37  tff(c_40600, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3) | ~v4_relat_1('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_40590])).
% 17.05/9.37  tff(c_44205, plain, (![A_3]: (r1_tarski('#skF_4', A_3) | ~v4_relat_1('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_44172, c_40600])).
% 17.05/9.37  tff(c_44442, plain, (r1_tarski('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))))), inference(resolution, [status(thm)], [c_44203, c_44205])).
% 17.05/9.37  tff(c_44214, plain, (u1_struct_0('#skF_1')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_44172, c_40566])).
% 17.05/9.37  tff(c_41026, plain, (![B_1417]: (k1_relset_1(B_1417, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')=k1_xboole_0 | ~r1_tarski(k1_xboole_0, B_1417))), inference(demodulation, [status(thm), theory('equality')], [c_40552, c_40552, c_27371])).
% 17.05/9.37  tff(c_27370, plain, (v1_funct_2('#skF_4', k1_xboole_0, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | k1_relset_1(k1_xboole_0, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')!=k1_xboole_0 | ~r1_tarski(k1_relat_1('#skF_4'), k1_xboole_0)), inference(resolution, [status(thm)], [c_27339, c_26])).
% 17.05/9.37  tff(c_41110, plain, (v1_funct_2('#skF_4', k1_xboole_0, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | k1_relset_1(k1_xboole_0, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6, c_40552, c_27370])).
% 17.05/9.37  tff(c_41111, plain, (k1_relset_1(k1_xboole_0, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_41110])).
% 17.05/9.37  tff(c_41114, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_41026, c_41111])).
% 17.05/9.37  tff(c_41118, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_41114])).
% 17.05/9.37  tff(c_41119, plain, (v1_funct_2('#skF_4', k1_xboole_0, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(splitRight, [status(thm)], [c_41110])).
% 17.05/9.37  tff(c_43976, plain, (v1_funct_2('#skF_4', k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_43973, c_41119])).
% 17.05/9.37  tff(c_44188, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44172, c_44172, c_43976])).
% 17.05/9.37  tff(c_44186, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44172, c_44172, c_43980])).
% 17.05/9.37  tff(c_40565, plain, (v1_funct_2('#skF_4', k1_xboole_0, u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40552, c_34755])).
% 17.05/9.37  tff(c_44209, plain, (v1_funct_2('#skF_4', '#skF_4', u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44172, c_40565])).
% 17.05/9.37  tff(c_40714, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_40552, c_34753])).
% 17.05/9.37  tff(c_44204, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_44172, c_40714])).
% 17.05/9.37  tff(c_40953, plain, (![B_2252]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_2252, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))))) | ~r1_tarski(k1_xboole_0, B_2252))), inference(demodulation, [status(thm), theory('equality')], [c_40552, c_27256])).
% 17.05/9.37  tff(c_41007, plain, (![B_2252]: (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0 | k1_relset_1(B_2252, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')=B_2252 | ~v1_funct_2('#skF_4', B_2252, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~r1_tarski(k1_xboole_0, B_2252))), inference(resolution, [status(thm)], [c_40953, c_32])).
% 17.05/9.37  tff(c_44336, plain, (![B_2252]: (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))='#skF_4' | k1_relset_1(B_2252, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')=B_2252 | ~v1_funct_2('#skF_4', B_2252, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~r1_tarski('#skF_4', B_2252))), inference(demodulation, [status(thm), theory('equality')], [c_44172, c_44172, c_41007])).
% 17.05/9.37  tff(c_44337, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))='#skF_4'), inference(splitLeft, [status(thm)], [c_44336])).
% 17.05/9.37  tff(c_40957, plain, (![A_43]: (v5_pre_topc('#skF_4', A_43, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', A_43, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0(A_43), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_43), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0(A_43), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(A_43) | ~v2_pre_topc(A_43) | ~r1_tarski(k1_xboole_0, u1_struct_0(A_43)))), inference(resolution, [status(thm)], [c_40953, c_56])).
% 17.05/9.37  tff(c_40999, plain, (![A_43]: (v5_pre_topc('#skF_4', A_43, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', A_43, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0(A_43), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_43), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0(A_43), u1_struct_0('#skF_2')) | ~l1_pre_topc(A_43) | ~v2_pre_topc(A_43) | ~r1_tarski(k1_xboole_0, u1_struct_0(A_43)))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_64, c_40957])).
% 17.05/9.37  tff(c_44895, plain, (![A_2356]: (v5_pre_topc('#skF_4', A_2356, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', A_2356, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0(A_2356), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2356), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0(A_2356), u1_struct_0('#skF_2')) | ~l1_pre_topc(A_2356) | ~v2_pre_topc(A_2356) | ~r1_tarski('#skF_4', u1_struct_0(A_2356)))), inference(demodulation, [status(thm), theory('equality')], [c_44172, c_44337, c_40999])).
% 17.05/9.37  tff(c_44904, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski('#skF_4', u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_44214, c_44895])).
% 17.05/9.37  tff(c_44909, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_44214, c_78, c_76, c_44209, c_44214, c_44204, c_44188, c_44214, c_27217, c_44904])).
% 17.05/9.37  tff(c_44025, plain, (v1_pre_topc(g1_pre_topc(k1_xboole_0, u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_43973, c_149])).
% 17.05/9.37  tff(c_44737, plain, (v1_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_44172, c_44025])).
% 17.05/9.37  tff(c_44738, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_44737])).
% 17.05/9.37  tff(c_44741, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_120, c_44738])).
% 17.05/9.37  tff(c_44745, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_44741])).
% 17.05/9.37  tff(c_44747, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_44737])).
% 17.05/9.37  tff(c_44022, plain, (v2_pre_topc(g1_pre_topc(k1_xboole_0, u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_43973, c_46])).
% 17.05/9.37  tff(c_44861, plain, (v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_44747, c_44172, c_44022])).
% 17.05/9.37  tff(c_44862, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_44861])).
% 17.05/9.37  tff(c_44865, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_46, c_44862])).
% 17.05/9.37  tff(c_44869, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_44865])).
% 17.05/9.37  tff(c_44871, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_44861])).
% 17.05/9.37  tff(c_40961, plain, (![A_28]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_28), u1_pre_topc(A_28)), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', A_28, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_28), u1_pre_topc(A_28))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_28), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))))) | ~v1_funct_2('#skF_4', u1_struct_0(A_28), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_28) | ~v2_pre_topc(A_28) | ~r1_tarski(k1_xboole_0, u1_struct_0(g1_pre_topc(u1_struct_0(A_28), u1_pre_topc(A_28)))))), inference(resolution, [status(thm)], [c_40953, c_52])).
% 17.05/9.37  tff(c_41002, plain, (![A_28]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_28), u1_pre_topc(A_28)), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', A_28, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_28), u1_pre_topc(A_28))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_28), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))))) | ~v1_funct_2('#skF_4', u1_struct_0(A_28), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_28) | ~v2_pre_topc(A_28) | ~r1_tarski(k1_xboole_0, u1_struct_0(g1_pre_topc(u1_struct_0(A_28), u1_pre_topc(A_28)))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_40961])).
% 17.05/9.37  tff(c_45007, plain, (![A_2366]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_2366), u1_pre_topc(A_2366)), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', A_2366, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_2366), u1_pre_topc(A_2366))), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2366), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_2366), '#skF_4') | ~l1_pre_topc(A_2366) | ~v2_pre_topc(A_2366) | ~r1_tarski('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_2366), u1_pre_topc(A_2366)))))), inference(demodulation, [status(thm), theory('equality')], [c_44172, c_44871, c_44747, c_44337, c_44337, c_44337, c_41002])).
% 17.05/9.37  tff(c_45019, plain, (v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_44214, c_45007])).
% 17.05/9.37  tff(c_45027, plain, (v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_44442, c_44214, c_78, c_76, c_44188, c_44214, c_44214, c_44186, c_44214, c_44909, c_45019])).
% 17.05/9.37  tff(c_45028, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_44197, c_45027])).
% 17.05/9.37  tff(c_45031, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_44183, c_45028])).
% 17.05/9.37  tff(c_45035, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_45031])).
% 17.05/9.37  tff(c_45037, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))!='#skF_4'), inference(splitRight, [status(thm)], [c_44336])).
% 17.05/9.37  tff(c_45175, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44190, c_45037])).
% 17.05/9.37  tff(c_45176, plain, (u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1')))=k1_xboole_0), inference(splitRight, [status(thm)], [c_40791])).
% 17.05/9.37  tff(c_40563, plain, (v2_pre_topc(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40552, c_34774])).
% 17.05/9.37  tff(c_40562, plain, (l1_pre_topc(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40552, c_34778])).
% 17.05/9.37  tff(c_45178, plain, (v1_funct_2('#skF_4', k1_xboole_0, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_45176, c_40564])).
% 17.05/9.37  tff(c_45390, plain, (![D_2372, A_2373, B_2374]: (v5_pre_topc(D_2372, A_2373, g1_pre_topc(u1_struct_0(B_2374), u1_pre_topc(B_2374))) | ~v5_pre_topc(D_2372, A_2373, B_2374) | ~m1_subset_1(D_2372, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2373), u1_struct_0(g1_pre_topc(u1_struct_0(B_2374), u1_pre_topc(B_2374)))))) | ~v1_funct_2(D_2372, u1_struct_0(A_2373), u1_struct_0(g1_pre_topc(u1_struct_0(B_2374), u1_pre_topc(B_2374)))) | ~m1_subset_1(D_2372, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2373), u1_struct_0(B_2374)))) | ~v1_funct_2(D_2372, u1_struct_0(A_2373), u1_struct_0(B_2374)) | ~v1_funct_1(D_2372) | ~l1_pre_topc(B_2374) | ~v2_pre_topc(B_2374) | ~l1_pre_topc(A_2373) | ~v2_pre_topc(A_2373))), inference(cnfTransformation, [status(thm)], [f_163])).
% 17.05/9.37  tff(c_45394, plain, (![A_2373]: (v5_pre_topc('#skF_4', A_2373, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', A_2373, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0(A_2373), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2373), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0(A_2373), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(A_2373) | ~v2_pre_topc(A_2373) | ~r1_tarski(k1_xboole_0, u1_struct_0(A_2373)))), inference(resolution, [status(thm)], [c_40570, c_45390])).
% 17.05/9.37  tff(c_53663, plain, (![A_2689]: (v5_pre_topc('#skF_4', A_2689, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', A_2689, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0(A_2689), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2689), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0(A_2689), u1_struct_0('#skF_2')) | ~l1_pre_topc(A_2689) | ~v2_pre_topc(A_2689) | ~r1_tarski(k1_xboole_0, u1_struct_0(A_2689)))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_64, c_45394])).
% 17.05/9.37  tff(c_53669, plain, (v5_pre_topc('#skF_4', g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1')), '#skF_2') | ~v1_funct_2('#skF_4', k1_xboole_0, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1'))), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1'))), u1_struct_0('#skF_2')) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1'))) | ~r1_tarski(k1_xboole_0, u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_45176, c_53663])).
% 17.05/9.37  tff(c_53675, plain, (v5_pre_topc('#skF_4', g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_45176, c_40563, c_40562, c_40565, c_45176, c_40714, c_45176, c_45178, c_53669])).
% 17.05/9.37  tff(c_53676, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1')), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_40929, c_53675])).
% 17.05/9.37  tff(c_40861, plain, (![B_2248]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_2248, u1_struct_0('#skF_2')))) | ~r1_tarski(k1_xboole_0, B_2248))), inference(demodulation, [status(thm), theory('equality')], [c_40552, c_27257])).
% 17.05/9.37  tff(c_40865, plain, (![A_28]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_28), u1_pre_topc(A_28)), '#skF_2') | ~v5_pre_topc('#skF_4', A_28, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_28), u1_pre_topc(A_28))), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_28), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0(A_28), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(A_28) | ~v2_pre_topc(A_28) | ~r1_tarski(k1_xboole_0, u1_struct_0(g1_pre_topc(u1_struct_0(A_28), u1_pre_topc(A_28)))))), inference(resolution, [status(thm)], [c_40861, c_52])).
% 17.05/9.37  tff(c_53801, plain, (![A_2698]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_2698), u1_pre_topc(A_2698)), '#skF_2') | ~v5_pre_topc('#skF_4', A_2698, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_2698), u1_pre_topc(A_2698))), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2698), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0(A_2698), u1_struct_0('#skF_2')) | ~l1_pre_topc(A_2698) | ~v2_pre_topc(A_2698) | ~r1_tarski(k1_xboole_0, u1_struct_0(g1_pre_topc(u1_struct_0(A_2698), u1_pre_topc(A_2698)))))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_64, c_40865])).
% 17.05/9.37  tff(c_53810, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1'))), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(k1_xboole_0, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_40566, c_53801])).
% 17.05/9.37  tff(c_53815, plain, (v5_pre_topc('#skF_4', g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_1')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_45176, c_40566, c_78, c_76, c_40565, c_40566, c_40714, c_40566, c_40565, c_45176, c_27217, c_40566, c_53810])).
% 17.05/9.37  tff(c_53817, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53676, c_53815])).
% 17.05/9.37  tff(c_53818, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_34746])).
% 17.05/9.37  tff(c_53852, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_53818, c_87])).
% 17.05/9.37  tff(c_53850, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_53818, c_91])).
% 17.05/9.37  tff(c_53915, plain, (k1_xboole_0='#skF_4' | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), k1_xboole_0) | u1_struct_0('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_53850, c_24])).
% 17.05/9.37  tff(c_53941, plain, (k1_xboole_0='#skF_4' | u1_struct_0('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_53852, c_53915])).
% 17.05/9.37  tff(c_53949, plain, (u1_struct_0('#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_53941])).
% 17.05/9.37  tff(c_53819, plain, (u1_struct_0('#skF_1')!=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_34746])).
% 17.05/9.37  tff(c_53998, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_53949, c_53819])).
% 17.05/9.37  tff(c_53996, plain, (v1_funct_2('#skF_4', k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_53949, c_53852])).
% 17.05/9.37  tff(c_53839, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_4')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_53818, c_34703])).
% 17.05/9.37  tff(c_53995, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_53949, c_53850])).
% 17.05/9.37  tff(c_54070, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_4', k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_53995, c_30])).
% 17.05/9.37  tff(c_54102, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_53996, c_53839, c_54070])).
% 17.05/9.37  tff(c_54104, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53998, c_54102])).
% 17.05/9.37  tff(c_54105, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_53941])).
% 17.05/9.37  tff(c_53846, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_53818, c_27218])).
% 17.05/9.37  tff(c_56387, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_54105, c_53846])).
% 17.05/9.37  tff(c_53856, plain, (v2_pre_topc(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_53818, c_46])).
% 17.05/9.37  tff(c_53869, plain, (v2_pre_topc(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_53856])).
% 17.05/9.37  tff(c_54110, plain, (v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_54105, c_53869])).
% 17.05/9.37  tff(c_53862, plain, (l1_pre_topc(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_53818, c_120])).
% 17.05/9.37  tff(c_53873, plain, (l1_pre_topc(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_53862])).
% 17.05/9.37  tff(c_54112, plain, (l1_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_54105, c_53873])).
% 17.05/9.37  tff(c_54113, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54105, c_53852])).
% 17.05/9.37  tff(c_53851, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_53818, c_62])).
% 17.05/9.37  tff(c_54114, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_54105, c_53851])).
% 17.05/9.37  tff(c_54107, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_54105, c_53850])).
% 17.05/9.37  tff(c_53844, plain, (![B_1408]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_1408, k1_xboole_0))) | ~r1_tarski(k1_relat_1('#skF_4'), B_1408))), inference(demodulation, [status(thm), theory('equality')], [c_53818, c_27257])).
% 17.05/9.37  tff(c_54350, plain, (![B_1408]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_1408, '#skF_4'))) | ~r1_tarski(k1_relat_1('#skF_4'), B_1408))), inference(demodulation, [status(thm), theory('equality')], [c_54105, c_53844])).
% 17.05/9.37  tff(c_54400, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_54105, c_53846])).
% 17.05/9.37  tff(c_54116, plain, (u1_struct_0('#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_54105, c_53818])).
% 17.05/9.37  tff(c_54229, plain, (k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))), '#skF_4')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54116, c_27228])).
% 17.05/9.37  tff(c_54569, plain, (u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))='#skF_4' | u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54229, c_54116, c_54105, c_54116, c_34743])).
% 17.05/9.37  tff(c_54570, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_54569])).
% 17.05/9.37  tff(c_54620, plain, (v1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_54570, c_149])).
% 17.05/9.37  tff(c_54745, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_54620])).
% 17.05/9.37  tff(c_54751, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_120, c_54745])).
% 17.05/9.37  tff(c_54755, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_54751])).
% 17.05/9.37  tff(c_54757, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_54620])).
% 17.05/9.37  tff(c_54617, plain, (v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_54570, c_46])).
% 17.05/9.37  tff(c_54829, plain, (v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_54757, c_54617])).
% 17.05/9.37  tff(c_54830, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_54829])).
% 17.05/9.37  tff(c_54833, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_54830])).
% 17.05/9.37  tff(c_54837, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_54833])).
% 17.05/9.37  tff(c_54839, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_54829])).
% 17.05/9.37  tff(c_54403, plain, (![A_2720]: (v1_funct_2('#skF_4', A_2720, '#skF_4') | A_2720='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_2720, '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_54105, c_54105, c_54105, c_54105, c_54105, c_22])).
% 17.05/9.37  tff(c_54414, plain, (![B_2721]: (v1_funct_2('#skF_4', B_2721, '#skF_4') | B_2721='#skF_4' | ~r1_tarski(k1_relat_1('#skF_4'), B_2721))), inference(resolution, [status(thm)], [c_54350, c_54403])).
% 17.05/9.37  tff(c_54433, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_4') | k1_relat_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_6, c_54414])).
% 17.05/9.37  tff(c_54434, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(splitLeft, [status(thm)], [c_54433])).
% 17.05/9.37  tff(c_54120, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54105, c_34691])).
% 17.05/9.37  tff(c_54211, plain, (k1_relat_1('#skF_4')='#skF_4' | ~r1_tarski('#skF_4', k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_54120, c_2])).
% 17.05/9.37  tff(c_54304, plain, (~r1_tarski('#skF_4', k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_54211])).
% 17.05/9.37  tff(c_54440, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54434, c_54304])).
% 17.05/9.37  tff(c_54451, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_54440])).
% 17.05/9.37  tff(c_54452, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_54433])).
% 17.05/9.37  tff(c_54571, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_54570, c_54114])).
% 17.05/9.37  tff(c_53887, plain, (![D_2702, A_2703, B_2704]: (v5_pre_topc(D_2702, g1_pre_topc(u1_struct_0(A_2703), u1_pre_topc(A_2703)), B_2704) | ~v5_pre_topc(D_2702, A_2703, B_2704) | ~m1_subset_1(D_2702, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2703), u1_pre_topc(A_2703))), u1_struct_0(B_2704)))) | ~v1_funct_2(D_2702, u1_struct_0(g1_pre_topc(u1_struct_0(A_2703), u1_pre_topc(A_2703))), u1_struct_0(B_2704)) | ~m1_subset_1(D_2702, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2703), u1_struct_0(B_2704)))) | ~v1_funct_2(D_2702, u1_struct_0(A_2703), u1_struct_0(B_2704)) | ~v1_funct_1(D_2702) | ~l1_pre_topc(B_2704) | ~v2_pre_topc(B_2704) | ~l1_pre_topc(A_2703) | ~v2_pre_topc(A_2703))), inference(cnfTransformation, [status(thm)], [f_134])).
% 17.05/9.37  tff(c_53893, plain, (![D_2702, A_2703]: (v5_pre_topc(D_2702, g1_pre_topc(u1_struct_0(A_2703), u1_pre_topc(A_2703)), '#skF_2') | ~v5_pre_topc(D_2702, A_2703, '#skF_2') | ~m1_subset_1(D_2702, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2703), u1_pre_topc(A_2703))), k1_xboole_0))) | ~v1_funct_2(D_2702, u1_struct_0(g1_pre_topc(u1_struct_0(A_2703), u1_pre_topc(A_2703))), u1_struct_0('#skF_2')) | ~m1_subset_1(D_2702, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2703), u1_struct_0('#skF_2')))) | ~v1_funct_2(D_2702, u1_struct_0(A_2703), u1_struct_0('#skF_2')) | ~v1_funct_1(D_2702) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(A_2703) | ~v2_pre_topc(A_2703))), inference(superposition, [status(thm), theory('equality')], [c_53818, c_53887])).
% 17.05/9.37  tff(c_53897, plain, (![D_2702, A_2703]: (v5_pre_topc(D_2702, g1_pre_topc(u1_struct_0(A_2703), u1_pre_topc(A_2703)), '#skF_2') | ~v5_pre_topc(D_2702, A_2703, '#skF_2') | ~m1_subset_1(D_2702, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2703), u1_pre_topc(A_2703))), k1_xboole_0))) | ~v1_funct_2(D_2702, u1_struct_0(g1_pre_topc(u1_struct_0(A_2703), u1_pre_topc(A_2703))), k1_xboole_0) | ~m1_subset_1(D_2702, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2703), k1_xboole_0))) | ~v1_funct_2(D_2702, u1_struct_0(A_2703), k1_xboole_0) | ~v1_funct_1(D_2702) | ~l1_pre_topc(A_2703) | ~v2_pre_topc(A_2703))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_53818, c_53818, c_53818, c_53893])).
% 17.05/9.37  tff(c_55628, plain, (![D_2804, A_2805]: (v5_pre_topc(D_2804, g1_pre_topc(u1_struct_0(A_2805), u1_pre_topc(A_2805)), '#skF_2') | ~v5_pre_topc(D_2804, A_2805, '#skF_2') | ~m1_subset_1(D_2804, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2805), u1_pre_topc(A_2805))), '#skF_4'))) | ~v1_funct_2(D_2804, u1_struct_0(g1_pre_topc(u1_struct_0(A_2805), u1_pre_topc(A_2805))), '#skF_4') | ~m1_subset_1(D_2804, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2805), '#skF_4'))) | ~v1_funct_2(D_2804, u1_struct_0(A_2805), '#skF_4') | ~v1_funct_1(D_2804) | ~l1_pre_topc(A_2805) | ~v2_pre_topc(A_2805))), inference(demodulation, [status(thm), theory('equality')], [c_54105, c_54105, c_54105, c_54105, c_53897])).
% 17.05/9.37  tff(c_55638, plain, (![A_2805]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_2805), u1_pre_topc(A_2805)), '#skF_2') | ~v5_pre_topc('#skF_4', A_2805, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_2805), u1_pre_topc(A_2805))), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2805), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_2805), '#skF_4') | ~v1_funct_1('#skF_4') | ~l1_pre_topc(A_2805) | ~v2_pre_topc(A_2805) | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0(A_2805), u1_pre_topc(A_2805)))))), inference(resolution, [status(thm)], [c_54350, c_55628])).
% 17.05/9.37  tff(c_55651, plain, (![A_2806]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_2806), u1_pre_topc(A_2806)), '#skF_2') | ~v5_pre_topc('#skF_4', A_2806, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_2806), u1_pre_topc(A_2806))), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2806), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_2806), '#skF_4') | ~l1_pre_topc(A_2806) | ~v2_pre_topc(A_2806) | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0(A_2806), u1_pre_topc(A_2806)))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_55638])).
% 17.05/9.37  tff(c_55657, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_54570, c_55651])).
% 17.05/9.37  tff(c_55667, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_78, c_76, c_54113, c_54107, c_54452, c_54570, c_27217, c_55657])).
% 17.05/9.37  tff(c_53841, plain, (![B_1408]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_1408, u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2')))))) | ~r1_tarski(k1_relat_1('#skF_4'), B_1408))), inference(demodulation, [status(thm), theory('equality')], [c_53818, c_27256])).
% 17.05/9.37  tff(c_54454, plain, (![B_1408]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_1408, u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))))) | ~r1_tarski(k1_relat_1('#skF_4'), B_1408))), inference(demodulation, [status(thm), theory('equality')], [c_54105, c_53841])).
% 17.05/9.37  tff(c_54305, plain, (![D_2714, A_2715, B_2716]: (v5_pre_topc(D_2714, A_2715, g1_pre_topc(u1_struct_0(B_2716), u1_pre_topc(B_2716))) | ~v5_pre_topc(D_2714, A_2715, B_2716) | ~m1_subset_1(D_2714, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2715), u1_struct_0(g1_pre_topc(u1_struct_0(B_2716), u1_pre_topc(B_2716)))))) | ~v1_funct_2(D_2714, u1_struct_0(A_2715), u1_struct_0(g1_pre_topc(u1_struct_0(B_2716), u1_pre_topc(B_2716)))) | ~m1_subset_1(D_2714, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2715), u1_struct_0(B_2716)))) | ~v1_funct_2(D_2714, u1_struct_0(A_2715), u1_struct_0(B_2716)) | ~v1_funct_1(D_2714) | ~l1_pre_topc(B_2716) | ~v2_pre_topc(B_2716) | ~l1_pre_topc(A_2715) | ~v2_pre_topc(A_2715))), inference(cnfTransformation, [status(thm)], [f_163])).
% 17.05/9.37  tff(c_54311, plain, (![D_2714, A_2715]: (v5_pre_topc(D_2714, A_2715, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc(D_2714, A_2715, '#skF_2') | ~m1_subset_1(D_2714, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2715), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))))) | ~v1_funct_2(D_2714, u1_struct_0(A_2715), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1(D_2714, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2715), u1_struct_0('#skF_2')))) | ~v1_funct_2(D_2714, u1_struct_0(A_2715), u1_struct_0('#skF_2')) | ~v1_funct_1(D_2714) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(A_2715) | ~v2_pre_topc(A_2715))), inference(superposition, [status(thm), theory('equality')], [c_54116, c_54305])).
% 17.05/9.37  tff(c_55839, plain, (![D_2820, A_2821]: (v5_pre_topc(D_2820, A_2821, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc(D_2820, A_2821, '#skF_2') | ~m1_subset_1(D_2820, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2821), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))))) | ~v1_funct_2(D_2820, u1_struct_0(A_2821), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~m1_subset_1(D_2820, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2821), '#skF_4'))) | ~v1_funct_2(D_2820, u1_struct_0(A_2821), '#skF_4') | ~v1_funct_1(D_2820) | ~l1_pre_topc(A_2821) | ~v2_pre_topc(A_2821))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_54116, c_54116, c_54116, c_54116, c_54311])).
% 17.05/9.37  tff(c_55846, plain, (![A_2821]: (v5_pre_topc('#skF_4', A_2821, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', A_2821, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0(A_2821), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2821), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_2821), '#skF_4') | ~v1_funct_1('#skF_4') | ~l1_pre_topc(A_2821) | ~v2_pre_topc(A_2821) | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(A_2821)))), inference(resolution, [status(thm)], [c_54454, c_55839])).
% 17.05/9.37  tff(c_55875, plain, (![A_2824]: (v5_pre_topc('#skF_4', A_2824, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', A_2824, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0(A_2824), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2824), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_2824), '#skF_4') | ~l1_pre_topc(A_2824) | ~v2_pre_topc(A_2824) | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(A_2824)))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_55846])).
% 17.05/9.37  tff(c_55881, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_54570, c_55875])).
% 17.05/9.37  tff(c_55887, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_54570, c_54839, c_54757, c_54452, c_54570, c_54570, c_54571, c_55667, c_55881])).
% 17.05/9.37  tff(c_55888, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_54400, c_55887])).
% 17.05/9.37  tff(c_55893, plain, (~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_54350, c_55888])).
% 17.05/9.37  tff(c_55897, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_55893])).
% 17.05/9.37  tff(c_55898, plain, (u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))='#skF_4'), inference(splitRight, [status(thm)], [c_54569])).
% 17.05/9.37  tff(c_55902, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_55898, c_54114])).
% 17.05/9.37  tff(c_53848, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2'))))))), inference(demodulation, [status(thm), theory('equality')], [c_53818, c_60])).
% 17.05/9.37  tff(c_54129, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))))))), inference(demodulation, [status(thm), theory('equality')], [c_54105, c_53848])).
% 17.05/9.37  tff(c_55905, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_55898, c_54129])).
% 17.05/9.37  tff(c_56143, plain, (![D_2843, A_2844]: (v5_pre_topc(D_2843, g1_pre_topc(u1_struct_0(A_2844), u1_pre_topc(A_2844)), '#skF_2') | ~v5_pre_topc(D_2843, A_2844, '#skF_2') | ~m1_subset_1(D_2843, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2844), u1_pre_topc(A_2844))), '#skF_4'))) | ~v1_funct_2(D_2843, u1_struct_0(g1_pre_topc(u1_struct_0(A_2844), u1_pre_topc(A_2844))), '#skF_4') | ~m1_subset_1(D_2843, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2844), '#skF_4'))) | ~v1_funct_2(D_2843, u1_struct_0(A_2844), '#skF_4') | ~v1_funct_1(D_2843) | ~l1_pre_topc(A_2844) | ~v2_pre_topc(A_2844))), inference(demodulation, [status(thm), theory('equality')], [c_54105, c_54105, c_54105, c_54105, c_53897])).
% 17.05/9.37  tff(c_56146, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4') | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_55905, c_56143])).
% 17.05/9.37  tff(c_56159, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_64, c_54113, c_54107, c_55902, c_27217, c_56146])).
% 17.05/9.37  tff(c_54315, plain, (![D_2714, A_2715]: (v5_pre_topc(D_2714, A_2715, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc(D_2714, A_2715, '#skF_2') | ~m1_subset_1(D_2714, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2715), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))))) | ~v1_funct_2(D_2714, u1_struct_0(A_2715), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~m1_subset_1(D_2714, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2715), '#skF_4'))) | ~v1_funct_2(D_2714, u1_struct_0(A_2715), '#skF_4') | ~v1_funct_1(D_2714) | ~l1_pre_topc(A_2715) | ~v2_pre_topc(A_2715))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_54116, c_54116, c_54116, c_54116, c_54311])).
% 17.05/9.37  tff(c_56116, plain, (![D_2841, A_2842]: (v5_pre_topc(D_2841, A_2842, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc(D_2841, A_2842, '#skF_2') | ~m1_subset_1(D_2841, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2842), '#skF_4'))) | ~v1_funct_2(D_2841, u1_struct_0(A_2842), '#skF_4') | ~m1_subset_1(D_2841, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2842), '#skF_4'))) | ~v1_funct_2(D_2841, u1_struct_0(A_2842), '#skF_4') | ~v1_funct_1(D_2841) | ~l1_pre_topc(A_2842) | ~v2_pre_topc(A_2842))), inference(demodulation, [status(thm), theory('equality')], [c_55898, c_55898, c_54315])).
% 17.05/9.37  tff(c_56118, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4') | ~v1_funct_1('#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_55905, c_56116])).
% 17.05/9.37  tff(c_56130, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_55902, c_55905, c_56118])).
% 17.05/9.37  tff(c_56131, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_54400, c_56130])).
% 17.05/9.37  tff(c_56168, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_56159, c_56131])).
% 17.05/9.37  tff(c_56169, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_56168])).
% 17.05/9.37  tff(c_56174, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_56169])).
% 17.05/9.37  tff(c_56178, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_56174])).
% 17.05/9.37  tff(c_56179, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_56168])).
% 17.05/9.37  tff(c_56183, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_120, c_56179])).
% 17.05/9.37  tff(c_56187, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_56183])).
% 17.05/9.37  tff(c_56188, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_54211])).
% 17.05/9.37  tff(c_56193, plain, (k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_56188, c_54229])).
% 17.05/9.37  tff(c_56590, plain, (![B_2868, A_2869, C_2870]: (B_2868='#skF_4' | k1_relset_1(A_2869, B_2868, C_2870)=A_2869 | ~v1_funct_2(C_2870, A_2869, B_2868) | ~m1_subset_1(C_2870, k1_zfmisc_1(k2_zfmisc_1(A_2869, B_2868))))), inference(demodulation, [status(thm), theory('equality')], [c_54105, c_32])).
% 17.05/9.37  tff(c_56602, plain, (u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))='#skF_4' | k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))), '#skF_4')=u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))))), inference(resolution, [status(thm)], [c_54129, c_56590])).
% 17.05/9.37  tff(c_56613, plain, (u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))='#skF_4' | u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_54114, c_56193, c_56602])).
% 17.05/9.37  tff(c_56633, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))='#skF_4'), inference(splitLeft, [status(thm)], [c_56613])).
% 17.05/9.37  tff(c_56203, plain, (![A_78]: (k1_relat_1('#skF_4')=A_78 | ~r1_tarski(A_78, '#skF_4') | ~v4_relat_1('#skF_4', A_78) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_56188, c_115])).
% 17.05/9.37  tff(c_56310, plain, (![A_2851]: (A_2851='#skF_4' | ~r1_tarski(A_2851, '#skF_4') | ~v4_relat_1('#skF_4', A_2851))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_56188, c_56203])).
% 17.05/9.37  tff(c_56335, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))='#skF_4' | ~r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4')), inference(resolution, [status(thm)], [c_143, c_56310])).
% 17.05/9.37  tff(c_56561, plain, (~r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4')), inference(splitLeft, [status(thm)], [c_56335])).
% 17.05/9.37  tff(c_56634, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56633, c_56561])).
% 17.05/9.37  tff(c_56643, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_56634])).
% 17.05/9.37  tff(c_56645, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))!='#skF_4'), inference(splitRight, [status(thm)], [c_56613])).
% 17.05/9.37  tff(c_27322, plain, (![B_1416]: (k1_relset_1(B_1416, u1_struct_0('#skF_2'), '#skF_4')=k1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), B_1416))), inference(resolution, [status(thm)], [c_27258, c_18])).
% 17.05/9.37  tff(c_27326, plain, (![A_3]: (k1_relset_1(A_3, u1_struct_0('#skF_2'), '#skF_4')=k1_relat_1('#skF_4') | ~v4_relat_1('#skF_4', A_3) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_10, c_27322])).
% 17.05/9.37  tff(c_27333, plain, (![A_3]: (k1_relset_1(A_3, u1_struct_0('#skF_2'), '#skF_4')=k1_relat_1('#skF_4') | ~v4_relat_1('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_27326])).
% 17.05/9.37  tff(c_53840, plain, (![A_3]: (k1_relset_1(A_3, k1_xboole_0, '#skF_4')=k1_relat_1('#skF_4') | ~v4_relat_1('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_53818, c_27333])).
% 17.05/9.37  tff(c_56358, plain, (![A_2853]: (k1_relset_1(A_2853, '#skF_4', '#skF_4')='#skF_4' | ~v4_relat_1('#skF_4', A_2853))), inference(demodulation, [status(thm), theory('equality')], [c_56188, c_54105, c_53840])).
% 17.05/9.37  tff(c_56381, plain, (k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_143, c_56358])).
% 17.05/9.37  tff(c_56644, plain, (u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))='#skF_4'), inference(splitRight, [status(thm)], [c_56613])).
% 17.05/9.37  tff(c_56475, plain, (u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))='#skF_4' | k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))), '#skF_4')=u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_54116, c_54105, c_54116, c_34743])).
% 17.05/9.37  tff(c_56476, plain, (k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))), '#skF_4')=u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_56475])).
% 17.05/9.37  tff(c_56798, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_56381, c_56644, c_56476])).
% 17.05/9.37  tff(c_56799, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56645, c_56798])).
% 17.05/9.37  tff(c_56800, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))='#skF_4'), inference(splitRight, [status(thm)], [c_56335])).
% 17.05/9.37  tff(c_56853, plain, (v1_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_56800, c_149])).
% 17.05/9.37  tff(c_56962, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_56853])).
% 17.05/9.37  tff(c_56965, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_120, c_56962])).
% 17.05/9.37  tff(c_56969, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_56965])).
% 17.05/9.37  tff(c_56971, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_56853])).
% 17.05/9.37  tff(c_56850, plain, (v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_56800, c_46])).
% 17.05/9.37  tff(c_57022, plain, (v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_56971, c_56850])).
% 17.05/9.37  tff(c_57023, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_57022])).
% 17.05/9.37  tff(c_57026, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_57023])).
% 17.05/9.37  tff(c_57030, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_57026])).
% 17.05/9.37  tff(c_57032, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_57022])).
% 17.05/9.37  tff(c_27334, plain, (k1_relset_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'), '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_6, c_27322])).
% 17.05/9.37  tff(c_53842, plain, (k1_relset_1(k1_relat_1('#skF_4'), k1_xboole_0, '#skF_4')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_53818, c_27334])).
% 17.05/9.37  tff(c_54299, plain, (k1_relset_1(k1_relat_1('#skF_4'), '#skF_4', '#skF_4')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54105, c_53842])).
% 17.05/9.37  tff(c_56190, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_56188, c_56188, c_54299])).
% 17.05/9.37  tff(c_56276, plain, (![B_1408]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_1408, '#skF_4'))) | ~r1_tarski('#skF_4', B_1408))), inference(demodulation, [status(thm), theory('equality')], [c_56188, c_54105, c_53844])).
% 17.05/9.37  tff(c_56510, plain, (![C_2863, B_2864]: (v1_funct_2(C_2863, '#skF_4', B_2864) | k1_relset_1('#skF_4', B_2864, C_2863)!='#skF_4' | ~m1_subset_1(C_2863, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_2864))))), inference(demodulation, [status(thm), theory('equality')], [c_54105, c_54105, c_54105, c_54105, c_26])).
% 17.05/9.37  tff(c_56518, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4') | k1_relset_1('#skF_4', '#skF_4', '#skF_4')!='#skF_4' | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_56276, c_56510])).
% 17.05/9.37  tff(c_56524, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_56190, c_56518])).
% 17.05/9.37  tff(c_56805, plain, (v1_funct_2('#skF_4', '#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_56800, c_54114])).
% 17.05/9.37  tff(c_56394, plain, (![B_1408]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_1408, u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))))) | ~r1_tarski('#skF_4', B_1408))), inference(demodulation, [status(thm), theory('equality')], [c_56188, c_54105, c_53841])).
% 17.05/9.37  tff(c_54247, plain, (![D_2711, A_2712, B_2713]: (v5_pre_topc(D_2711, A_2712, B_2713) | ~v5_pre_topc(D_2711, A_2712, g1_pre_topc(u1_struct_0(B_2713), u1_pre_topc(B_2713))) | ~m1_subset_1(D_2711, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2712), u1_struct_0(g1_pre_topc(u1_struct_0(B_2713), u1_pre_topc(B_2713)))))) | ~v1_funct_2(D_2711, u1_struct_0(A_2712), u1_struct_0(g1_pre_topc(u1_struct_0(B_2713), u1_pre_topc(B_2713)))) | ~m1_subset_1(D_2711, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2712), u1_struct_0(B_2713)))) | ~v1_funct_2(D_2711, u1_struct_0(A_2712), u1_struct_0(B_2713)) | ~v1_funct_1(D_2711) | ~l1_pre_topc(B_2713) | ~v2_pre_topc(B_2713) | ~l1_pre_topc(A_2712) | ~v2_pre_topc(A_2712))), inference(cnfTransformation, [status(thm)], [f_163])).
% 17.05/9.37  tff(c_54253, plain, (![D_2711, A_2712]: (v5_pre_topc(D_2711, A_2712, '#skF_2') | ~v5_pre_topc(D_2711, A_2712, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_subset_1(D_2711, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2712), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))))) | ~v1_funct_2(D_2711, u1_struct_0(A_2712), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1(D_2711, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2712), u1_struct_0('#skF_2')))) | ~v1_funct_2(D_2711, u1_struct_0(A_2712), u1_struct_0('#skF_2')) | ~v1_funct_1(D_2711) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(A_2712) | ~v2_pre_topc(A_2712))), inference(superposition, [status(thm), theory('equality')], [c_54116, c_54247])).
% 17.05/9.37  tff(c_57592, plain, (![D_2934, A_2935]: (v5_pre_topc(D_2934, A_2935, '#skF_2') | ~v5_pre_topc(D_2934, A_2935, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~m1_subset_1(D_2934, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2935), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))))) | ~v1_funct_2(D_2934, u1_struct_0(A_2935), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~m1_subset_1(D_2934, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2935), '#skF_4'))) | ~v1_funct_2(D_2934, u1_struct_0(A_2935), '#skF_4') | ~v1_funct_1(D_2934) | ~l1_pre_topc(A_2935) | ~v2_pre_topc(A_2935))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_54116, c_54116, c_54116, c_54116, c_54253])).
% 17.05/9.37  tff(c_57599, plain, (![A_2935]: (v5_pre_topc('#skF_4', A_2935, '#skF_2') | ~v5_pre_topc('#skF_4', A_2935, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_2935), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2935), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_2935), '#skF_4') | ~v1_funct_1('#skF_4') | ~l1_pre_topc(A_2935) | ~v2_pre_topc(A_2935) | ~r1_tarski('#skF_4', u1_struct_0(A_2935)))), inference(resolution, [status(thm)], [c_56394, c_57592])).
% 17.05/9.37  tff(c_57610, plain, (![A_2936]: (v5_pre_topc('#skF_4', A_2936, '#skF_2') | ~v5_pre_topc('#skF_4', A_2936, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_2936), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2936), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_2936), '#skF_4') | ~l1_pre_topc(A_2936) | ~v2_pre_topc(A_2936) | ~r1_tarski('#skF_4', u1_struct_0(A_2936)))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_57599])).
% 17.05/9.37  tff(c_57619, plain, (v5_pre_topc('#skF_4', '#skF_2', '#skF_2') | ~v5_pre_topc('#skF_4', '#skF_2', g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', '#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), '#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~r1_tarski('#skF_4', u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_54116, c_57610])).
% 17.05/9.37  tff(c_57624, plain, (v5_pre_topc('#skF_4', '#skF_2', '#skF_2') | ~v5_pre_topc('#skF_4', '#skF_2', g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_54116, c_74, c_72, c_56524, c_54116, c_54116, c_56805, c_57619])).
% 17.05/9.37  tff(c_57625, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(splitLeft, [status(thm)], [c_57624])).
% 17.05/9.37  tff(c_57628, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_56276, c_57625])).
% 17.05/9.37  tff(c_57632, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_57628])).
% 17.05/9.37  tff(c_57634, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(splitRight, [status(thm)], [c_57624])).
% 17.05/9.37  tff(c_57512, plain, (![D_2926, A_2927]: (v5_pre_topc(D_2926, g1_pre_topc(u1_struct_0(A_2927), u1_pre_topc(A_2927)), '#skF_2') | ~v5_pre_topc(D_2926, A_2927, '#skF_2') | ~m1_subset_1(D_2926, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2927), u1_pre_topc(A_2927))), '#skF_4'))) | ~v1_funct_2(D_2926, u1_struct_0(g1_pre_topc(u1_struct_0(A_2927), u1_pre_topc(A_2927))), '#skF_4') | ~m1_subset_1(D_2926, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2927), '#skF_4'))) | ~v1_funct_2(D_2926, u1_struct_0(A_2927), '#skF_4') | ~v1_funct_1(D_2926) | ~l1_pre_topc(A_2927) | ~v2_pre_topc(A_2927))), inference(demodulation, [status(thm), theory('equality')], [c_54105, c_54105, c_54105, c_54105, c_53897])).
% 17.05/9.37  tff(c_57522, plain, (![A_2927]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_2927), u1_pre_topc(A_2927)), '#skF_2') | ~v5_pre_topc('#skF_4', A_2927, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_2927), u1_pre_topc(A_2927))), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2927), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_2927), '#skF_4') | ~v1_funct_1('#skF_4') | ~l1_pre_topc(A_2927) | ~v2_pre_topc(A_2927) | ~r1_tarski('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_2927), u1_pre_topc(A_2927)))))), inference(resolution, [status(thm)], [c_56276, c_57512])).
% 17.05/9.37  tff(c_57562, plain, (![A_2933]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_2933), u1_pre_topc(A_2933)), '#skF_2') | ~v5_pre_topc('#skF_4', A_2933, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_2933), u1_pre_topc(A_2933))), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2933), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_2933), '#skF_4') | ~l1_pre_topc(A_2933) | ~v2_pre_topc(A_2933) | ~r1_tarski('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_2933), u1_pre_topc(A_2933)))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_57522])).
% 17.05/9.37  tff(c_57568, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_4', '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_56800, c_57562])).
% 17.05/9.37  tff(c_57581, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_56800, c_78, c_76, c_54113, c_54107, c_56524, c_27217, c_57568])).
% 17.05/9.37  tff(c_56225, plain, (![D_2845, A_2846, B_2847]: (v5_pre_topc(D_2845, A_2846, g1_pre_topc(u1_struct_0(B_2847), u1_pre_topc(B_2847))) | ~v5_pre_topc(D_2845, A_2846, B_2847) | ~m1_subset_1(D_2845, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2846), u1_struct_0(g1_pre_topc(u1_struct_0(B_2847), u1_pre_topc(B_2847)))))) | ~v1_funct_2(D_2845, u1_struct_0(A_2846), u1_struct_0(g1_pre_topc(u1_struct_0(B_2847), u1_pre_topc(B_2847)))) | ~m1_subset_1(D_2845, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2846), u1_struct_0(B_2847)))) | ~v1_funct_2(D_2845, u1_struct_0(A_2846), u1_struct_0(B_2847)) | ~v1_funct_1(D_2845) | ~l1_pre_topc(B_2847) | ~v2_pre_topc(B_2847) | ~l1_pre_topc(A_2846) | ~v2_pre_topc(A_2846))), inference(cnfTransformation, [status(thm)], [f_163])).
% 17.05/9.37  tff(c_56231, plain, (![D_2845, A_2846]: (v5_pre_topc(D_2845, A_2846, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc(D_2845, A_2846, '#skF_2') | ~m1_subset_1(D_2845, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2846), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))))) | ~v1_funct_2(D_2845, u1_struct_0(A_2846), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1(D_2845, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2846), u1_struct_0('#skF_2')))) | ~v1_funct_2(D_2845, u1_struct_0(A_2846), u1_struct_0('#skF_2')) | ~v1_funct_1(D_2845) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(A_2846) | ~v2_pre_topc(A_2846))), inference(superposition, [status(thm), theory('equality')], [c_54116, c_56225])).
% 17.05/9.37  tff(c_57776, plain, (![D_2943, A_2944]: (v5_pre_topc(D_2943, A_2944, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc(D_2943, A_2944, '#skF_2') | ~m1_subset_1(D_2943, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2944), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))))) | ~v1_funct_2(D_2943, u1_struct_0(A_2944), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~m1_subset_1(D_2943, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2944), '#skF_4'))) | ~v1_funct_2(D_2943, u1_struct_0(A_2944), '#skF_4') | ~v1_funct_1(D_2943) | ~l1_pre_topc(A_2944) | ~v2_pre_topc(A_2944))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_54116, c_54116, c_54116, c_54116, c_56231])).
% 17.05/9.37  tff(c_57783, plain, (![A_2944]: (v5_pre_topc('#skF_4', A_2944, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', A_2944, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0(A_2944), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2944), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_2944), '#skF_4') | ~v1_funct_1('#skF_4') | ~l1_pre_topc(A_2944) | ~v2_pre_topc(A_2944) | ~r1_tarski('#skF_4', u1_struct_0(A_2944)))), inference(resolution, [status(thm)], [c_56394, c_57776])).
% 17.05/9.37  tff(c_57794, plain, (![A_2945]: (v5_pre_topc('#skF_4', A_2945, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', A_2945, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0(A_2945), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2945), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_2945), '#skF_4') | ~l1_pre_topc(A_2945) | ~v2_pre_topc(A_2945) | ~r1_tarski('#skF_4', u1_struct_0(A_2945)))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_57783])).
% 17.05/9.37  tff(c_57800, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~v1_funct_2('#skF_4', '#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~r1_tarski('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_56800, c_57794])).
% 17.05/9.37  tff(c_57806, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_56800, c_57032, c_56971, c_56524, c_56800, c_57634, c_56800, c_56805, c_57581, c_57800])).
% 17.05/9.37  tff(c_57808, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56387, c_57806])).
% 17.05/9.37  tff(c_57809, plain, (u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))='#skF_4'), inference(splitRight, [status(thm)], [c_56475])).
% 17.05/9.37  tff(c_57813, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_57809, c_54114])).
% 17.05/9.37  tff(c_54132, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54129, c_52])).
% 17.05/9.37  tff(c_54152, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~l1_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_64, c_54132])).
% 17.05/9.37  tff(c_58061, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_54110, c_54112, c_54113, c_57809, c_54107, c_57809, c_57813, c_57809, c_54152])).
% 17.05/9.37  tff(c_58062, plain, (~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_56387, c_58061])).
% 17.05/9.37  tff(c_56235, plain, (![D_2845, A_2846]: (v5_pre_topc(D_2845, A_2846, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc(D_2845, A_2846, '#skF_2') | ~m1_subset_1(D_2845, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2846), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))))) | ~v1_funct_2(D_2845, u1_struct_0(A_2846), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~m1_subset_1(D_2845, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2846), '#skF_4'))) | ~v1_funct_2(D_2845, u1_struct_0(A_2846), '#skF_4') | ~v1_funct_1(D_2845) | ~l1_pre_topc(A_2846) | ~v2_pre_topc(A_2846))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_54116, c_54116, c_54116, c_54116, c_56231])).
% 17.05/9.37  tff(c_58074, plain, (![D_2967, A_2968]: (v5_pre_topc(D_2967, A_2968, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc(D_2967, A_2968, '#skF_2') | ~m1_subset_1(D_2967, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2968), '#skF_4'))) | ~v1_funct_2(D_2967, u1_struct_0(A_2968), '#skF_4') | ~m1_subset_1(D_2967, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2968), '#skF_4'))) | ~v1_funct_2(D_2967, u1_struct_0(A_2968), '#skF_4') | ~v1_funct_1(D_2967) | ~l1_pre_topc(A_2968) | ~v2_pre_topc(A_2968))), inference(demodulation, [status(thm), theory('equality')], [c_57809, c_57809, c_56235])).
% 17.05/9.37  tff(c_58083, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4') | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54107, c_58074])).
% 17.05/9.37  tff(c_58097, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_64, c_54113, c_54107, c_27217, c_58083])).
% 17.05/9.37  tff(c_58099, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58062, c_58097])).
% 17.05/9.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.05/9.37  
% 17.05/9.37  Inference rules
% 17.05/9.37  ----------------------
% 17.05/9.37  #Ref     : 0
% 17.05/9.37  #Sup     : 10334
% 17.05/9.37  #Fact    : 0
% 17.05/9.37  #Define  : 0
% 17.05/9.37  #Split   : 314
% 17.05/9.37  #Chain   : 0
% 17.05/9.37  #Close   : 0
% 17.05/9.37  
% 17.05/9.37  Ordering : KBO
% 17.05/9.37  
% 17.05/9.37  Simplification rules
% 17.05/9.37  ----------------------
% 17.05/9.37  #Subsume      : 2246
% 17.05/9.37  #Demod        : 34302
% 17.05/9.37  #Tautology    : 4972
% 17.05/9.37  #SimpNegUnit  : 775
% 17.05/9.37  #BackRed      : 1921
% 17.05/9.37  
% 17.05/9.37  #Partial instantiations: 0
% 17.05/9.37  #Strategies tried      : 1
% 17.05/9.37  
% 17.05/9.37  Timing (in seconds)
% 17.05/9.37  ----------------------
% 17.05/9.37  Preprocessing        : 0.34
% 17.05/9.37  Parsing              : 0.17
% 17.05/9.37  CNF conversion       : 0.03
% 17.05/9.37  Main loop            : 7.67
% 17.05/9.37  Inferencing          : 2.13
% 17.05/9.37  Reduction            : 3.48
% 17.05/9.37  Demodulation         : 2.71
% 17.05/9.37  BG Simplification    : 0.19
% 17.05/9.37  Subsumption          : 1.45
% 17.05/9.37  Abstraction          : 0.28
% 17.05/9.37  MUC search           : 0.00
% 17.05/9.37  Cooper               : 0.00
% 17.05/9.37  Total                : 8.53
% 17.05/9.37  Index Insertion      : 0.00
% 17.05/9.37  Index Deletion       : 0.00
% 17.05/9.37  Index Matching       : 0.00
% 17.05/9.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
