%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:12 EST 2020

% Result     : Theorem 23.80s
% Output     : CNFRefutation 24.36s
% Verified   : 
% Statistics : Number of formulae       :  437 (43390 expanded)
%              Number of leaves         :   36 (14223 expanded)
%              Depth                    :   25
%              Number of atoms          : 1223 (164929 expanded)
%              Number of equality atoms :  145 (32793 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_pre_topc > k1_relset_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_181,negated_conjecture,(
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

tff(f_93,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_81,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v1_pre_topc(g1_pre_topc(A,B))
        & l1_pre_topc(g1_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_69,axiom,(
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

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_122,axiom,(
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

tff(f_151,axiom,(
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

tff(c_68,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_66,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_52,plain,(
    '#skF_3' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_80,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_82,plain,
    ( v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_80])).

tff(c_290,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_74,plain,
    ( ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_84,plain,
    ( ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_74])).

tff(c_343,plain,(
    ~ v5_pre_topc('#skF_4','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_290,c_84])).

tff(c_40,plain,(
    ! [A_22] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(A_22),u1_pre_topc(A_22)))
      | ~ l1_pre_topc(A_22)
      | ~ v2_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_179,plain,(
    ! [A_84] :
      ( m1_subset_1(u1_pre_topc(A_84),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_84))))
      | ~ l1_pre_topc(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_34,plain,(
    ! [A_19,B_20] :
      ( l1_pre_topc(g1_pre_topc(A_19,B_20))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(k1_zfmisc_1(A_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_190,plain,(
    ! [A_84] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_84),u1_pre_topc(A_84)))
      | ~ l1_pre_topc(A_84) ) ),
    inference(resolution,[status(thm)],[c_179,c_34])).

tff(c_72,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_70,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_8,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_97,plain,(
    ! [A_67,B_68] :
      ( r1_tarski(A_67,B_68)
      | ~ m1_subset_1(A_67,k1_zfmisc_1(B_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_101,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(resolution,[status(thm)],[c_8,c_97])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_62,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_81,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_62])).

tff(c_60,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_85,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_60])).

tff(c_300,plain,(
    ! [A_106,B_107,C_108] :
      ( k1_relset_1(A_106,B_107,C_108) = k1_relat_1(C_108)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_316,plain,(
    k1_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_85,c_300])).

tff(c_807,plain,(
    ! [B_155,A_156,C_157] :
      ( k1_xboole_0 = B_155
      | k1_relset_1(A_156,B_155,C_157) = A_156
      | ~ v1_funct_2(C_157,A_156,B_155)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_156,B_155))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_817,plain,
    ( u1_struct_0('#skF_2') = k1_xboole_0
    | k1_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4') = u1_struct_0('#skF_1')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_85,c_807])).

tff(c_832,plain,
    ( u1_struct_0('#skF_2') = k1_xboole_0
    | u1_struct_0('#skF_1') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_316,c_817])).

tff(c_836,plain,(
    u1_struct_0('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_832])).

tff(c_374,plain,(
    ! [A_116,B_117,C_118] :
      ( m1_subset_1(k1_relset_1(A_116,B_117,C_118),k1_zfmisc_1(A_116))
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_397,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_316,c_374])).

tff(c_407,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_397])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_524,plain,(
    r1_tarski(k1_relat_1('#skF_4'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_407,c_10])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_527,plain,
    ( u1_struct_0('#skF_1') = k1_relat_1('#skF_4')
    | ~ r1_tarski(u1_struct_0('#skF_1'),k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_524,c_2])).

tff(c_544,plain,(
    ~ r1_tarski(u1_struct_0('#skF_1'),k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_527])).

tff(c_840,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_836,c_544])).

tff(c_857,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_840])).

tff(c_858,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_832])).

tff(c_870,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_858,c_81])).

tff(c_121,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_85,c_10])).

tff(c_867,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0('#skF_1'),k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_858,c_121])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_501,plain,(
    ! [C_123,A_124] :
      ( k1_xboole_0 = C_123
      | ~ v1_funct_2(C_123,A_124,k1_xboole_0)
      | k1_xboole_0 = A_124
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_124,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_515,plain,(
    ! [A_4,A_124] :
      ( k1_xboole_0 = A_4
      | ~ v1_funct_2(A_4,A_124,k1_xboole_0)
      | k1_xboole_0 = A_124
      | ~ r1_tarski(A_4,k2_zfmisc_1(A_124,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_12,c_501])).

tff(c_947,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),k1_xboole_0)
    | u1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_867,c_515])).

tff(c_955,plain,
    ( k1_xboole_0 = '#skF_4'
    | u1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_870,c_947])).

tff(c_958,plain,(
    u1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_955])).

tff(c_997,plain,(
    ~ r1_tarski(k1_xboole_0,k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_958,c_544])).

tff(c_1003,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_997])).

tff(c_1004,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_955])).

tff(c_1012,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1004,c_870])).

tff(c_1031,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1004,c_101])).

tff(c_58,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_1033,plain,(
    ! [A_3] : m1_subset_1('#skF_4',k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1004,c_8])).

tff(c_318,plain,(
    ! [A_106,B_107] : k1_relset_1(A_106,B_107,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_300])).

tff(c_400,plain,(
    ! [A_106,B_107] :
      ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(A_106))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_318,c_374])).

tff(c_410,plain,(
    ! [A_119] : m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(A_119)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_400])).

tff(c_433,plain,(
    ! [A_120] : r1_tarski(k1_relat_1(k1_xboole_0),A_120) ),
    inference(resolution,[status(thm)],[c_410,c_10])).

tff(c_108,plain,(
    ! [B_72,A_73] :
      ( B_72 = A_73
      | ~ r1_tarski(B_72,A_73)
      | ~ r1_tarski(A_73,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_113,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_101,c_108])).

tff(c_455,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_433,c_113])).

tff(c_459,plain,(
    ! [A_106,B_107] : k1_relset_1(A_106,B_107,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_455,c_318])).

tff(c_684,plain,(
    ! [C_140,B_141] :
      ( v1_funct_2(C_140,k1_xboole_0,B_141)
      | k1_relset_1(k1_xboole_0,B_141,C_140) != k1_xboole_0
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_696,plain,(
    ! [B_141] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_141)
      | k1_relset_1(k1_xboole_0,B_141,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_684])).

tff(c_701,plain,(
    ! [B_141] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_141) ),
    inference(demodulation,[status(thm),theory(equality)],[c_459,c_696])).

tff(c_1020,plain,(
    ! [B_141] : v1_funct_2('#skF_4','#skF_4',B_141) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1004,c_1004,c_701])).

tff(c_1026,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1004,c_1004,c_455])).

tff(c_1014,plain,(
    u1_struct_0('#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1004,c_858])).

tff(c_56,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_315,plain,(
    k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_300])).

tff(c_814,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0
    | k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') = u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(resolution,[status(thm)],[c_54,c_807])).

tff(c_829,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_315,c_814])).

tff(c_1386,plain,
    ( u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) = '#skF_4'
    | u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1026,c_1014,c_1004,c_829])).

tff(c_1387,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1386])).

tff(c_1309,plain,(
    ! [D_177,A_178,B_179] :
      ( v5_pre_topc(D_177,A_178,B_179)
      | ~ v5_pre_topc(D_177,g1_pre_topc(u1_struct_0(A_178),u1_pre_topc(A_178)),B_179)
      | ~ m1_subset_1(D_177,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_178),u1_pre_topc(A_178))),u1_struct_0(B_179))))
      | ~ v1_funct_2(D_177,u1_struct_0(g1_pre_topc(u1_struct_0(A_178),u1_pre_topc(A_178))),u1_struct_0(B_179))
      | ~ m1_subset_1(D_177,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_178),u1_struct_0(B_179))))
      | ~ v1_funct_2(D_177,u1_struct_0(A_178),u1_struct_0(B_179))
      | ~ v1_funct_1(D_177)
      | ~ l1_pre_topc(B_179)
      | ~ v2_pre_topc(B_179)
      | ~ l1_pre_topc(A_178)
      | ~ v2_pre_topc(A_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1313,plain,(
    ! [A_178,B_179] :
      ( v5_pre_topc('#skF_4',A_178,B_179)
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_178),u1_pre_topc(A_178)),B_179)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_178),u1_pre_topc(A_178))),u1_struct_0(B_179))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_178),u1_struct_0(B_179))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_178),u1_struct_0(B_179))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(B_179)
      | ~ v2_pre_topc(B_179)
      | ~ l1_pre_topc(A_178)
      | ~ v2_pre_topc(A_178) ) ),
    inference(resolution,[status(thm)],[c_1033,c_1309])).

tff(c_8079,plain,(
    ! [A_773,B_774] :
      ( v5_pre_topc('#skF_4',A_773,B_774)
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_773),u1_pre_topc(A_773)),B_774)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_773),u1_pre_topc(A_773))),u1_struct_0(B_774))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_773),u1_struct_0(B_774))
      | ~ l1_pre_topc(B_774)
      | ~ v2_pre_topc(B_774)
      | ~ l1_pre_topc(A_773)
      | ~ v2_pre_topc(A_773) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1033,c_1313])).

tff(c_8097,plain,(
    ! [A_773] :
      ( v5_pre_topc('#skF_4',A_773,'#skF_2')
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_773),u1_pre_topc(A_773)),'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_773),u1_pre_topc(A_773))),'#skF_4')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_773),u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_773)
      | ~ v2_pre_topc(A_773) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1014,c_8079])).

tff(c_8404,plain,(
    ! [A_784] :
      ( v5_pre_topc('#skF_4',A_784,'#skF_2')
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_784),u1_pre_topc(A_784)),'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_784),u1_pre_topc(A_784))),'#skF_4')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_784),'#skF_4')
      | ~ l1_pre_topc(A_784)
      | ~ v2_pre_topc(A_784) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_1014,c_8097])).

tff(c_8413,plain,
    ( v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ v1_funct_2('#skF_4','#skF_4','#skF_4')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1387,c_8404])).

tff(c_8428,plain,
    ( v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_1012,c_1020,c_8413])).

tff(c_8429,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_343,c_8428])).

tff(c_862,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_858,c_290])).

tff(c_1532,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1004,c_862])).

tff(c_1468,plain,
    ( l1_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1387,c_190])).

tff(c_1895,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1468])).

tff(c_1901,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_190,c_1895])).

tff(c_1907,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1901])).

tff(c_1909,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_1468])).

tff(c_1462,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1387,c_40])).

tff(c_2560,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1909,c_1462])).

tff(c_2561,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2560])).

tff(c_2567,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_2561])).

tff(c_2573,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_2567])).

tff(c_2575,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_2560])).

tff(c_1183,plain,(
    ! [D_168,A_169,B_170] :
      ( v5_pre_topc(D_168,A_169,B_170)
      | ~ v5_pre_topc(D_168,A_169,g1_pre_topc(u1_struct_0(B_170),u1_pre_topc(B_170)))
      | ~ m1_subset_1(D_168,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_169),u1_struct_0(g1_pre_topc(u1_struct_0(B_170),u1_pre_topc(B_170))))))
      | ~ v1_funct_2(D_168,u1_struct_0(A_169),u1_struct_0(g1_pre_topc(u1_struct_0(B_170),u1_pre_topc(B_170))))
      | ~ m1_subset_1(D_168,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_169),u1_struct_0(B_170))))
      | ~ v1_funct_2(D_168,u1_struct_0(A_169),u1_struct_0(B_170))
      | ~ v1_funct_1(D_168)
      | ~ l1_pre_topc(B_170)
      | ~ v2_pre_topc(B_170)
      | ~ l1_pre_topc(A_169)
      | ~ v2_pre_topc(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_1187,plain,(
    ! [A_169,B_170] :
      ( v5_pre_topc('#skF_4',A_169,B_170)
      | ~ v5_pre_topc('#skF_4',A_169,g1_pre_topc(u1_struct_0(B_170),u1_pre_topc(B_170)))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_169),u1_struct_0(g1_pre_topc(u1_struct_0(B_170),u1_pre_topc(B_170))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_169),u1_struct_0(B_170))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_169),u1_struct_0(B_170))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(B_170)
      | ~ v2_pre_topc(B_170)
      | ~ l1_pre_topc(A_169)
      | ~ v2_pre_topc(A_169) ) ),
    inference(resolution,[status(thm)],[c_1033,c_1183])).

tff(c_9435,plain,(
    ! [A_814,B_815] :
      ( v5_pre_topc('#skF_4',A_814,B_815)
      | ~ v5_pre_topc('#skF_4',A_814,g1_pre_topc(u1_struct_0(B_815),u1_pre_topc(B_815)))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_814),u1_struct_0(g1_pre_topc(u1_struct_0(B_815),u1_pre_topc(B_815))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_814),u1_struct_0(B_815))
      | ~ l1_pre_topc(B_815)
      | ~ v2_pre_topc(B_815)
      | ~ l1_pre_topc(A_814)
      | ~ v2_pre_topc(A_814) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1033,c_1187])).

tff(c_9441,plain,(
    ! [B_815] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_815)
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0(B_815),u1_pre_topc(B_815)))
      | ~ v1_funct_2('#skF_4','#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(B_815),u1_pre_topc(B_815))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_815))
      | ~ l1_pre_topc(B_815)
      | ~ v2_pre_topc(B_815)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1387,c_9435])).

tff(c_9524,plain,(
    ! [B_817] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_817)
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0(B_817),u1_pre_topc(B_817)))
      | ~ l1_pre_topc(B_817)
      | ~ v2_pre_topc(B_817) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2575,c_1909,c_1020,c_1387,c_1020,c_9441])).

tff(c_9575,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1014,c_9524])).

tff(c_9624,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_1532,c_9575])).

tff(c_9626,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8429,c_9624])).

tff(c_9627,plain,(
    u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1386])).

tff(c_869,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_858,c_56])).

tff(c_1013,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1004,c_869])).

tff(c_9630,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9627,c_1013])).

tff(c_9782,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1004,c_862])).

tff(c_880,plain,
    ( v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_858,c_40])).

tff(c_900,plain,(
    v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_880])).

tff(c_1009,plain,(
    v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1004,c_900])).

tff(c_886,plain,
    ( l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_858,c_190])).

tff(c_904,plain,(
    l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_886])).

tff(c_1010,plain,(
    l1_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1004,c_904])).

tff(c_11211,plain,(
    ! [A_998,A_999,B_1000] :
      ( v5_pre_topc(A_998,A_999,B_1000)
      | ~ v5_pre_topc(A_998,g1_pre_topc(u1_struct_0(A_999),u1_pre_topc(A_999)),B_1000)
      | ~ v1_funct_2(A_998,u1_struct_0(g1_pre_topc(u1_struct_0(A_999),u1_pre_topc(A_999))),u1_struct_0(B_1000))
      | ~ m1_subset_1(A_998,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_999),u1_struct_0(B_1000))))
      | ~ v1_funct_2(A_998,u1_struct_0(A_999),u1_struct_0(B_1000))
      | ~ v1_funct_1(A_998)
      | ~ l1_pre_topc(B_1000)
      | ~ v2_pre_topc(B_1000)
      | ~ l1_pre_topc(A_999)
      | ~ v2_pre_topc(A_999)
      | ~ r1_tarski(A_998,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_999),u1_pre_topc(A_999))),u1_struct_0(B_1000))) ) ),
    inference(resolution,[status(thm)],[c_12,c_1309])).

tff(c_11225,plain,(
    ! [A_998,A_999] :
      ( v5_pre_topc(A_998,A_999,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc(A_998,g1_pre_topc(u1_struct_0(A_999),u1_pre_topc(A_999)),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v1_funct_2(A_998,u1_struct_0(g1_pre_topc(u1_struct_0(A_999),u1_pre_topc(A_999))),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1(A_998,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_999),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))))
      | ~ v1_funct_2(A_998,u1_struct_0(A_999),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
      | ~ v1_funct_1(A_998)
      | ~ l1_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_999)
      | ~ v2_pre_topc(A_999)
      | ~ r1_tarski(A_998,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_999),u1_pre_topc(A_999))),'#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9627,c_11211])).

tff(c_11332,plain,(
    ! [A_1005,A_1006] :
      ( v5_pre_topc(A_1005,A_1006,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc(A_1005,g1_pre_topc(u1_struct_0(A_1006),u1_pre_topc(A_1006)),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v1_funct_2(A_1005,u1_struct_0(g1_pre_topc(u1_struct_0(A_1006),u1_pre_topc(A_1006))),'#skF_4')
      | ~ m1_subset_1(A_1005,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1006),'#skF_4')))
      | ~ v1_funct_2(A_1005,u1_struct_0(A_1006),'#skF_4')
      | ~ v1_funct_1(A_1005)
      | ~ l1_pre_topc(A_1006)
      | ~ v2_pre_topc(A_1006)
      | ~ r1_tarski(A_1005,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1006),u1_pre_topc(A_1006))),'#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1009,c_1010,c_9627,c_9627,c_9627,c_11225])).

tff(c_11335,plain,
    ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),'#skF_4')))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_9782,c_11332])).

tff(c_11347,plain,(
    v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1031,c_72,c_70,c_58,c_1012,c_1033,c_9630,c_11335])).

tff(c_11585,plain,(
    ! [A_1033,A_1034,B_1035] :
      ( v5_pre_topc(A_1033,A_1034,B_1035)
      | ~ v5_pre_topc(A_1033,A_1034,g1_pre_topc(u1_struct_0(B_1035),u1_pre_topc(B_1035)))
      | ~ v1_funct_2(A_1033,u1_struct_0(A_1034),u1_struct_0(g1_pre_topc(u1_struct_0(B_1035),u1_pre_topc(B_1035))))
      | ~ m1_subset_1(A_1033,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1034),u1_struct_0(B_1035))))
      | ~ v1_funct_2(A_1033,u1_struct_0(A_1034),u1_struct_0(B_1035))
      | ~ v1_funct_1(A_1033)
      | ~ l1_pre_topc(B_1035)
      | ~ v2_pre_topc(B_1035)
      | ~ l1_pre_topc(A_1034)
      | ~ v2_pre_topc(A_1034)
      | ~ r1_tarski(A_1033,k2_zfmisc_1(u1_struct_0(A_1034),u1_struct_0(g1_pre_topc(u1_struct_0(B_1035),u1_pre_topc(B_1035))))) ) ),
    inference(resolution,[status(thm)],[c_12,c_1183])).

tff(c_11609,plain,(
    ! [A_1033,A_1034] :
      ( v5_pre_topc(A_1033,A_1034,'#skF_2')
      | ~ v5_pre_topc(A_1033,A_1034,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v1_funct_2(A_1033,u1_struct_0(A_1034),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1(A_1033,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1034),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(A_1033,u1_struct_0(A_1034),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(A_1033)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_1034)
      | ~ v2_pre_topc(A_1034)
      | ~ r1_tarski(A_1033,k2_zfmisc_1(u1_struct_0(A_1034),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1014,c_11585])).

tff(c_15653,plain,(
    ! [A_1413,A_1414] :
      ( v5_pre_topc(A_1413,A_1414,'#skF_2')
      | ~ v5_pre_topc(A_1413,A_1414,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ m1_subset_1(A_1413,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1414),'#skF_4')))
      | ~ v1_funct_2(A_1413,u1_struct_0(A_1414),'#skF_4')
      | ~ v1_funct_1(A_1413)
      | ~ l1_pre_topc(A_1414)
      | ~ v2_pre_topc(A_1414)
      | ~ r1_tarski(A_1413,k2_zfmisc_1(u1_struct_0(A_1414),'#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9627,c_68,c_66,c_1014,c_1014,c_9627,c_1014,c_1014,c_11609])).

tff(c_15680,plain,(
    ! [A_1414] :
      ( v5_pre_topc('#skF_4',A_1414,'#skF_2')
      | ~ v5_pre_topc('#skF_4',A_1414,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1414),'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(A_1414)
      | ~ v2_pre_topc(A_1414)
      | ~ r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0(A_1414),'#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1033,c_15653])).

tff(c_15716,plain,(
    ! [A_1415] :
      ( v5_pre_topc('#skF_4',A_1415,'#skF_2')
      | ~ v5_pre_topc('#skF_4',A_1415,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1415),'#skF_4')
      | ~ l1_pre_topc(A_1415)
      | ~ v2_pre_topc(A_1415) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1031,c_58,c_15680])).

tff(c_15750,plain,
    ( v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_11347,c_15716])).

tff(c_15781,plain,(
    v5_pre_topc('#skF_4','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_1012,c_15750])).

tff(c_15783,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_343,c_15781])).

tff(c_15784,plain,(
    u1_struct_0('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_527])).

tff(c_15796,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15784,c_121])).

tff(c_15799,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15784,c_81])).

tff(c_15798,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15784,c_56])).

tff(c_152,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))) ),
    inference(resolution,[status(thm)],[c_54,c_10])).

tff(c_344,plain,(
    ! [A_111,B_112,A_113] :
      ( k1_relset_1(A_111,B_112,A_113) = k1_relat_1(A_113)
      | ~ r1_tarski(A_113,k2_zfmisc_1(A_111,B_112)) ) ),
    inference(resolution,[status(thm)],[c_12,c_300])).

tff(c_359,plain,(
    k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_152,c_344])).

tff(c_16430,plain,(
    k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15784,c_359])).

tff(c_15794,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15784,c_152])).

tff(c_16020,plain,(
    ! [B_1430,A_1431,C_1432] :
      ( k1_xboole_0 = B_1430
      | k1_relset_1(A_1431,B_1430,C_1432) = A_1431
      | ~ v1_funct_2(C_1432,A_1431,B_1430)
      | ~ m1_subset_1(C_1432,k1_zfmisc_1(k2_zfmisc_1(A_1431,B_1430))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_16752,plain,(
    ! [B_1519,A_1520,A_1521] :
      ( k1_xboole_0 = B_1519
      | k1_relset_1(A_1520,B_1519,A_1521) = A_1520
      | ~ v1_funct_2(A_1521,A_1520,B_1519)
      | ~ r1_tarski(A_1521,k2_zfmisc_1(A_1520,B_1519)) ) ),
    inference(resolution,[status(thm)],[c_12,c_16020])).

tff(c_16759,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0
    | k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') = u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(resolution,[status(thm)],[c_15794,c_16752])).

tff(c_16782,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15798,c_16430,c_16759])).

tff(c_16803,plain,(
    u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_16782])).

tff(c_15797,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15784,c_85])).

tff(c_15810,plain,
    ( v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_15784,c_40])).

tff(c_15830,plain,(
    v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_15810])).

tff(c_15816,plain,
    ( l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_15784,c_190])).

tff(c_15834,plain,(
    l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_15816])).

tff(c_15791,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15784,c_290])).

tff(c_15795,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15784,c_54])).

tff(c_16308,plain,(
    ! [D_1463,A_1464,B_1465] :
      ( v5_pre_topc(D_1463,A_1464,B_1465)
      | ~ v5_pre_topc(D_1463,A_1464,g1_pre_topc(u1_struct_0(B_1465),u1_pre_topc(B_1465)))
      | ~ m1_subset_1(D_1463,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1464),u1_struct_0(g1_pre_topc(u1_struct_0(B_1465),u1_pre_topc(B_1465))))))
      | ~ v1_funct_2(D_1463,u1_struct_0(A_1464),u1_struct_0(g1_pre_topc(u1_struct_0(B_1465),u1_pre_topc(B_1465))))
      | ~ m1_subset_1(D_1463,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1464),u1_struct_0(B_1465))))
      | ~ v1_funct_2(D_1463,u1_struct_0(A_1464),u1_struct_0(B_1465))
      | ~ v1_funct_1(D_1463)
      | ~ l1_pre_topc(B_1465)
      | ~ v2_pre_topc(B_1465)
      | ~ l1_pre_topc(A_1464)
      | ~ v2_pre_topc(A_1464) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_16311,plain,
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
    inference(resolution,[status(thm)],[c_15795,c_16308])).

tff(c_16335,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15830,c_15834,c_68,c_66,c_58,c_15798,c_15791,c_16311])).

tff(c_17655,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15799,c_16803,c_15797,c_16803,c_16335])).

tff(c_16162,plain,(
    ! [D_1448,A_1449,B_1450] :
      ( v5_pre_topc(D_1448,A_1449,B_1450)
      | ~ v5_pre_topc(D_1448,g1_pre_topc(u1_struct_0(A_1449),u1_pre_topc(A_1449)),B_1450)
      | ~ m1_subset_1(D_1448,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1449),u1_pre_topc(A_1449))),u1_struct_0(B_1450))))
      | ~ v1_funct_2(D_1448,u1_struct_0(g1_pre_topc(u1_struct_0(A_1449),u1_pre_topc(A_1449))),u1_struct_0(B_1450))
      | ~ m1_subset_1(D_1448,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1449),u1_struct_0(B_1450))))
      | ~ v1_funct_2(D_1448,u1_struct_0(A_1449),u1_struct_0(B_1450))
      | ~ v1_funct_1(D_1448)
      | ~ l1_pre_topc(B_1450)
      | ~ v2_pre_topc(B_1450)
      | ~ l1_pre_topc(A_1449)
      | ~ v2_pre_topc(A_1449) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_18013,plain,(
    ! [A_1638,A_1639,B_1640] :
      ( v5_pre_topc(A_1638,A_1639,B_1640)
      | ~ v5_pre_topc(A_1638,g1_pre_topc(u1_struct_0(A_1639),u1_pre_topc(A_1639)),B_1640)
      | ~ v1_funct_2(A_1638,u1_struct_0(g1_pre_topc(u1_struct_0(A_1639),u1_pre_topc(A_1639))),u1_struct_0(B_1640))
      | ~ m1_subset_1(A_1638,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1639),u1_struct_0(B_1640))))
      | ~ v1_funct_2(A_1638,u1_struct_0(A_1639),u1_struct_0(B_1640))
      | ~ v1_funct_1(A_1638)
      | ~ l1_pre_topc(B_1640)
      | ~ v2_pre_topc(B_1640)
      | ~ l1_pre_topc(A_1639)
      | ~ v2_pre_topc(A_1639)
      | ~ r1_tarski(A_1638,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1639),u1_pre_topc(A_1639))),u1_struct_0(B_1640))) ) ),
    inference(resolution,[status(thm)],[c_12,c_16162])).

tff(c_18042,plain,(
    ! [A_1638,B_1640] :
      ( v5_pre_topc(A_1638,'#skF_1',B_1640)
      | ~ v5_pre_topc(A_1638,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_1640)
      | ~ v1_funct_2(A_1638,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_1640))
      | ~ m1_subset_1(A_1638,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_1640))))
      | ~ v1_funct_2(A_1638,u1_struct_0('#skF_1'),u1_struct_0(B_1640))
      | ~ v1_funct_1(A_1638)
      | ~ l1_pre_topc(B_1640)
      | ~ v2_pre_topc(B_1640)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r1_tarski(A_1638,k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(B_1640))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15784,c_18013])).

tff(c_23307,plain,(
    ! [A_2117,B_2118] :
      ( v5_pre_topc(A_2117,'#skF_1',B_2118)
      | ~ v5_pre_topc(A_2117,g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),B_2118)
      | ~ m1_subset_1(A_2117,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_2118))))
      | ~ v1_funct_2(A_2117,k1_relat_1('#skF_4'),u1_struct_0(B_2118))
      | ~ v1_funct_1(A_2117)
      | ~ l1_pre_topc(B_2118)
      | ~ v2_pre_topc(B_2118)
      | ~ r1_tarski(A_2117,k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_2118))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16803,c_72,c_70,c_15784,c_15784,c_16803,c_15784,c_15784,c_18042])).

tff(c_23336,plain,
    ( v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | ~ r1_tarski('#skF_4',k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_15797,c_23307])).

tff(c_23375,plain,(
    v5_pre_topc('#skF_4','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15796,c_68,c_66,c_58,c_15799,c_17655,c_23336])).

tff(c_23377,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_343,c_23375])).

tff(c_23378,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_16782])).

tff(c_23383,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23378,c_15798])).

tff(c_23381,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23378,c_15794])).

tff(c_23496,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),k1_xboole_0)
    | u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_23381,c_515])).

tff(c_23511,plain,
    ( k1_xboole_0 = '#skF_4'
    | u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_23383,c_23496])).

tff(c_23514,plain,(
    u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_23511])).

tff(c_23379,plain,(
    u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) != k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_16782])).

tff(c_23552,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_23514,c_23379])).

tff(c_16,plain,(
    ! [A_9,B_10,C_11] :
      ( m1_subset_1(k1_relset_1(A_9,B_10,C_11),k1_zfmisc_1(A_9))
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_469,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))) ),
    inference(superposition,[status(thm),theory(equality)],[c_315,c_16])).

tff(c_479,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_469])).

tff(c_16007,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15784,c_479])).

tff(c_16014,plain,(
    r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))) ),
    inference(resolution,[status(thm)],[c_16007,c_10])).

tff(c_23554,plain,(
    r1_tarski(k1_relat_1('#skF_4'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23514,c_16014])).

tff(c_23642,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_23554,c_113])).

tff(c_23648,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_23552,c_23642])).

tff(c_23649,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_23511])).

tff(c_191,plain,(
    ! [A_84] :
      ( r1_tarski(u1_pre_topc(A_84),k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_pre_topc(A_84) ) ),
    inference(resolution,[status(thm)],[c_179,c_10])).

tff(c_23435,plain,
    ( r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),k1_zfmisc_1(k1_xboole_0))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_23378,c_191])).

tff(c_24712,plain,
    ( r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),k1_zfmisc_1('#skF_4'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23649,c_23435])).

tff(c_24713,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_24712])).

tff(c_24719,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_190,c_24713])).

tff(c_24725,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_24719])).

tff(c_24727,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_24712])).

tff(c_23432,plain,
    ( v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_23378,c_40])).

tff(c_25521,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24727,c_23649,c_23432])).

tff(c_25522,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_25521])).

tff(c_25528,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_25522])).

tff(c_25534,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_25528])).

tff(c_25536,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_25521])).

tff(c_23676,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23649,c_23649,c_455])).

tff(c_23652,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23649,c_23383])).

tff(c_24318,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23676,c_23652])).

tff(c_23697,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23676,c_15791])).

tff(c_23653,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23649,c_23378])).

tff(c_15891,plain,(
    ! [C_1418,B_1419] :
      ( v1_funct_2(C_1418,k1_xboole_0,B_1419)
      | k1_relset_1(k1_xboole_0,B_1419,C_1418) != k1_xboole_0
      | ~ m1_subset_1(C_1418,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_1419))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_15903,plain,(
    ! [B_1419] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_1419)
      | k1_relset_1(k1_xboole_0,B_1419,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_15891])).

tff(c_15908,plain,(
    ! [B_1419] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_1419) ),
    inference(demodulation,[status(thm),theory(equality)],[c_459,c_15903])).

tff(c_23671,plain,(
    ! [B_1419] : v1_funct_2('#skF_4','#skF_4',B_1419) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23649,c_23649,c_15908])).

tff(c_23716,plain,(
    u1_struct_0('#skF_1') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23676,c_15784])).

tff(c_16183,plain,(
    ! [A_1449,B_1450] :
      ( v5_pre_topc(k1_xboole_0,A_1449,B_1450)
      | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(A_1449),u1_pre_topc(A_1449)),B_1450)
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(A_1449),u1_pre_topc(A_1449))),u1_struct_0(B_1450))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1449),u1_struct_0(B_1450))))
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(A_1449),u1_struct_0(B_1450))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ l1_pre_topc(B_1450)
      | ~ v2_pre_topc(B_1450)
      | ~ l1_pre_topc(A_1449)
      | ~ v2_pre_topc(A_1449) ) ),
    inference(resolution,[status(thm)],[c_8,c_16162])).

tff(c_16192,plain,(
    ! [A_1449,B_1450] :
      ( v5_pre_topc(k1_xboole_0,A_1449,B_1450)
      | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(A_1449),u1_pre_topc(A_1449)),B_1450)
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(A_1449),u1_pre_topc(A_1449))),u1_struct_0(B_1450))
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(A_1449),u1_struct_0(B_1450))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ l1_pre_topc(B_1450)
      | ~ v2_pre_topc(B_1450)
      | ~ l1_pre_topc(A_1449)
      | ~ v2_pre_topc(A_1449) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_16183])).

tff(c_24141,plain,(
    ! [A_2155,B_2156] :
      ( v5_pre_topc('#skF_4',A_2155,B_2156)
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_2155),u1_pre_topc(A_2155)),B_2156)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_2155),u1_pre_topc(A_2155))),u1_struct_0(B_2156))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_2155),u1_struct_0(B_2156))
      | ~ l1_pre_topc(B_2156)
      | ~ v2_pre_topc(B_2156)
      | ~ l1_pre_topc(A_2155)
      | ~ v2_pre_topc(A_2155) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_23649,c_23649,c_23649,c_23649,c_23649,c_16192])).

tff(c_24144,plain,(
    ! [B_2156] :
      ( v5_pre_topc('#skF_4','#skF_1',B_2156)
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_2156)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),u1_struct_0(B_2156))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0(B_2156))
      | ~ l1_pre_topc(B_2156)
      | ~ v2_pre_topc(B_2156)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23716,c_24141])).

tff(c_27209,plain,(
    ! [B_2403] :
      ( v5_pre_topc('#skF_4','#skF_1',B_2403)
      | ~ v5_pre_topc('#skF_4',g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),B_2403)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),u1_struct_0(B_2403))
      | ~ l1_pre_topc(B_2403)
      | ~ v2_pre_topc(B_2403) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_23671,c_23716,c_23716,c_24144])).

tff(c_27215,plain,
    ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4',g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),'#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_23653,c_27209])).

tff(c_27221,plain,(
    v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25536,c_24727,c_24318,c_23697,c_27215])).

tff(c_16332,plain,(
    ! [A_1464,B_1465] :
      ( v5_pre_topc(k1_xboole_0,A_1464,B_1465)
      | ~ v5_pre_topc(k1_xboole_0,A_1464,g1_pre_topc(u1_struct_0(B_1465),u1_pre_topc(B_1465)))
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(A_1464),u1_struct_0(g1_pre_topc(u1_struct_0(B_1465),u1_pre_topc(B_1465))))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1464),u1_struct_0(B_1465))))
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(A_1464),u1_struct_0(B_1465))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ l1_pre_topc(B_1465)
      | ~ v2_pre_topc(B_1465)
      | ~ l1_pre_topc(A_1464)
      | ~ v2_pre_topc(A_1464) ) ),
    inference(resolution,[status(thm)],[c_8,c_16308])).

tff(c_16344,plain,(
    ! [A_1464,B_1465] :
      ( v5_pre_topc(k1_xboole_0,A_1464,B_1465)
      | ~ v5_pre_topc(k1_xboole_0,A_1464,g1_pre_topc(u1_struct_0(B_1465),u1_pre_topc(B_1465)))
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(A_1464),u1_struct_0(g1_pre_topc(u1_struct_0(B_1465),u1_pre_topc(B_1465))))
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(A_1464),u1_struct_0(B_1465))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ l1_pre_topc(B_1465)
      | ~ v2_pre_topc(B_1465)
      | ~ l1_pre_topc(A_1464)
      | ~ v2_pre_topc(A_1464) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_16332])).

tff(c_24394,plain,(
    ! [A_2170,B_2171] :
      ( v5_pre_topc('#skF_4',A_2170,B_2171)
      | ~ v5_pre_topc('#skF_4',A_2170,g1_pre_topc(u1_struct_0(B_2171),u1_pre_topc(B_2171)))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_2170),u1_struct_0(g1_pre_topc(u1_struct_0(B_2171),u1_pre_topc(B_2171))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_2170),u1_struct_0(B_2171))
      | ~ l1_pre_topc(B_2171)
      | ~ v2_pre_topc(B_2171)
      | ~ l1_pre_topc(A_2170)
      | ~ v2_pre_topc(A_2170) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_23649,c_23649,c_23649,c_23649,c_23649,c_16344])).

tff(c_24409,plain,(
    ! [B_2171] :
      ( v5_pre_topc('#skF_4','#skF_1',B_2171)
      | ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0(B_2171),u1_pre_topc(B_2171)))
      | ~ v1_funct_2('#skF_4','#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(B_2171),u1_pre_topc(B_2171))))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0(B_2171))
      | ~ l1_pre_topc(B_2171)
      | ~ v2_pre_topc(B_2171)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23716,c_24394])).

tff(c_24423,plain,(
    ! [B_2171] :
      ( v5_pre_topc('#skF_4','#skF_1',B_2171)
      | ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0(B_2171),u1_pre_topc(B_2171)))
      | ~ l1_pre_topc(B_2171)
      | ~ v2_pre_topc(B_2171) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_23671,c_23716,c_23671,c_24409])).

tff(c_27262,plain,
    ( v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_27221,c_24423])).

tff(c_27268,plain,(
    v5_pre_topc('#skF_4','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_27262])).

tff(c_27270,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_343,c_27268])).

tff(c_27271,plain,(
    v5_pre_topc('#skF_4','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_27282,plain,(
    ! [A_2410,B_2411,C_2412] :
      ( k1_relset_1(A_2410,B_2411,C_2412) = k1_relat_1(C_2412)
      | ~ m1_subset_1(C_2412,k1_zfmisc_1(k2_zfmisc_1(A_2410,B_2411))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_27298,plain,(
    k1_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_85,c_27282])).

tff(c_27822,plain,(
    ! [B_2468,A_2469,C_2470] :
      ( k1_xboole_0 = B_2468
      | k1_relset_1(A_2469,B_2468,C_2470) = A_2469
      | ~ v1_funct_2(C_2470,A_2469,B_2468)
      | ~ m1_subset_1(C_2470,k1_zfmisc_1(k2_zfmisc_1(A_2469,B_2468))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_27832,plain,
    ( u1_struct_0('#skF_2') = k1_xboole_0
    | k1_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4') = u1_struct_0('#skF_1')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_85,c_27822])).

tff(c_27847,plain,
    ( u1_struct_0('#skF_2') = k1_xboole_0
    | u1_struct_0('#skF_1') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_27298,c_27832])).

tff(c_27851,plain,(
    u1_struct_0('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_27847])).

tff(c_27356,plain,(
    ! [A_2420,B_2421,C_2422] :
      ( m1_subset_1(k1_relset_1(A_2420,B_2421,C_2422),k1_zfmisc_1(A_2420))
      | ~ m1_subset_1(C_2422,k1_zfmisc_1(k2_zfmisc_1(A_2420,B_2421))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_27379,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_27298,c_27356])).

tff(c_27389,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_27379])).

tff(c_27517,plain,(
    r1_tarski(k1_relat_1('#skF_4'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_27389,c_10])).

tff(c_27520,plain,
    ( u1_struct_0('#skF_1') = k1_relat_1('#skF_4')
    | ~ r1_tarski(u1_struct_0('#skF_1'),k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_27517,c_2])).

tff(c_27545,plain,(
    ~ r1_tarski(u1_struct_0('#skF_1'),k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_27520])).

tff(c_27855,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27851,c_27545])).

tff(c_27872,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_27855])).

tff(c_27873,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_27847])).

tff(c_27885,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27873,c_81])).

tff(c_27882,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0('#skF_1'),k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27873,c_121])).

tff(c_27469,plain,(
    ! [C_2425,A_2426] :
      ( k1_xboole_0 = C_2425
      | ~ v1_funct_2(C_2425,A_2426,k1_xboole_0)
      | k1_xboole_0 = A_2426
      | ~ m1_subset_1(C_2425,k1_zfmisc_1(k2_zfmisc_1(A_2426,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_27483,plain,(
    ! [A_4,A_2426] :
      ( k1_xboole_0 = A_4
      | ~ v1_funct_2(A_4,A_2426,k1_xboole_0)
      | k1_xboole_0 = A_2426
      | ~ r1_tarski(A_4,k2_zfmisc_1(A_2426,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_12,c_27469])).

tff(c_27976,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),k1_xboole_0)
    | u1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_27882,c_27483])).

tff(c_27984,plain,
    ( k1_xboole_0 = '#skF_4'
    | u1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_27885,c_27976])).

tff(c_27987,plain,(
    u1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_27984])).

tff(c_28032,plain,(
    ~ r1_tarski(k1_xboole_0,k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27987,c_27545])).

tff(c_28038,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_28032])).

tff(c_28039,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_27984])).

tff(c_28046,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28039,c_27885])).

tff(c_28068,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28039,c_101])).

tff(c_28070,plain,(
    ! [A_3] : m1_subset_1('#skF_4',k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28039,c_8])).

tff(c_27300,plain,(
    ! [A_2410,B_2411] : k1_relset_1(A_2410,B_2411,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_27282])).

tff(c_27382,plain,(
    ! [A_2410,B_2411] :
      ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(A_2410))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_2410,B_2411))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27300,c_27356])).

tff(c_27411,plain,(
    ! [A_2423] : m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(A_2423)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_27382])).

tff(c_27434,plain,(
    ! [A_2424] : r1_tarski(k1_relat_1(k1_xboole_0),A_2424) ),
    inference(resolution,[status(thm)],[c_27411,c_10])).

tff(c_27456,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_27434,c_113])).

tff(c_27460,plain,(
    ! [A_2410,B_2411] : k1_relset_1(A_2410,B_2411,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_27456,c_27300])).

tff(c_27524,plain,(
    ! [C_2430,B_2431] :
      ( v1_funct_2(C_2430,k1_xboole_0,B_2431)
      | k1_relset_1(k1_xboole_0,B_2431,C_2430) != k1_xboole_0
      | ~ m1_subset_1(C_2430,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_2431))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_27536,plain,(
    ! [B_2431] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_2431)
      | k1_relset_1(k1_xboole_0,B_2431,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_27524])).

tff(c_27541,plain,(
    ! [B_2431] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_2431) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27460,c_27536])).

tff(c_28059,plain,(
    ! [B_2431] : v1_funct_2('#skF_4','#skF_4',B_2431) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28039,c_28039,c_27541])).

tff(c_28048,plain,(
    u1_struct_0('#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28039,c_27873])).

tff(c_28063,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28039,c_28039,c_27456])).

tff(c_27297,plain,(
    k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_27282])).

tff(c_27829,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0
    | k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') = u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(resolution,[status(thm)],[c_54,c_27822])).

tff(c_27844,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_27297,c_27829])).

tff(c_28412,plain,
    ( u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) = '#skF_4'
    | u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28063,c_28048,c_28039,c_27844])).

tff(c_28413,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_28412])).

tff(c_28149,plain,(
    ! [D_2475,A_2476,B_2477] :
      ( v5_pre_topc(D_2475,g1_pre_topc(u1_struct_0(A_2476),u1_pre_topc(A_2476)),B_2477)
      | ~ v5_pre_topc(D_2475,A_2476,B_2477)
      | ~ m1_subset_1(D_2475,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2476),u1_pre_topc(A_2476))),u1_struct_0(B_2477))))
      | ~ v1_funct_2(D_2475,u1_struct_0(g1_pre_topc(u1_struct_0(A_2476),u1_pre_topc(A_2476))),u1_struct_0(B_2477))
      | ~ m1_subset_1(D_2475,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2476),u1_struct_0(B_2477))))
      | ~ v1_funct_2(D_2475,u1_struct_0(A_2476),u1_struct_0(B_2477))
      | ~ v1_funct_1(D_2475)
      | ~ l1_pre_topc(B_2477)
      | ~ v2_pre_topc(B_2477)
      | ~ l1_pre_topc(A_2476)
      | ~ v2_pre_topc(A_2476) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_30463,plain,(
    ! [A_2718,A_2719,B_2720] :
      ( v5_pre_topc(A_2718,g1_pre_topc(u1_struct_0(A_2719),u1_pre_topc(A_2719)),B_2720)
      | ~ v5_pre_topc(A_2718,A_2719,B_2720)
      | ~ v1_funct_2(A_2718,u1_struct_0(g1_pre_topc(u1_struct_0(A_2719),u1_pre_topc(A_2719))),u1_struct_0(B_2720))
      | ~ m1_subset_1(A_2718,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2719),u1_struct_0(B_2720))))
      | ~ v1_funct_2(A_2718,u1_struct_0(A_2719),u1_struct_0(B_2720))
      | ~ v1_funct_1(A_2718)
      | ~ l1_pre_topc(B_2720)
      | ~ v2_pre_topc(B_2720)
      | ~ l1_pre_topc(A_2719)
      | ~ v2_pre_topc(A_2719)
      | ~ r1_tarski(A_2718,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2719),u1_pre_topc(A_2719))),u1_struct_0(B_2720))) ) ),
    inference(resolution,[status(thm)],[c_12,c_28149])).

tff(c_30485,plain,(
    ! [A_2718,B_2720] :
      ( v5_pre_topc(A_2718,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_2720)
      | ~ v5_pre_topc(A_2718,'#skF_1',B_2720)
      | ~ v1_funct_2(A_2718,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_2720))
      | ~ m1_subset_1(A_2718,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_2720))))
      | ~ v1_funct_2(A_2718,u1_struct_0('#skF_1'),u1_struct_0(B_2720))
      | ~ v1_funct_1(A_2718)
      | ~ l1_pre_topc(B_2720)
      | ~ v2_pre_topc(B_2720)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r1_tarski(A_2718,k2_zfmisc_1('#skF_4',u1_struct_0(B_2720))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28413,c_30463])).

tff(c_30967,plain,(
    ! [A_2756,B_2757] :
      ( v5_pre_topc(A_2756,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_2757)
      | ~ v5_pre_topc(A_2756,'#skF_1',B_2757)
      | ~ v1_funct_2(A_2756,'#skF_4',u1_struct_0(B_2757))
      | ~ m1_subset_1(A_2756,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_2757))))
      | ~ v1_funct_2(A_2756,u1_struct_0('#skF_1'),u1_struct_0(B_2757))
      | ~ v1_funct_1(A_2756)
      | ~ l1_pre_topc(B_2757)
      | ~ v2_pre_topc(B_2757)
      | ~ r1_tarski(A_2756,k2_zfmisc_1('#skF_4',u1_struct_0(B_2757))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_28413,c_30485])).

tff(c_30989,plain,(
    ! [A_2756] :
      ( v5_pre_topc(A_2756,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
      | ~ v5_pre_topc(A_2756,'#skF_1','#skF_2')
      | ~ v1_funct_2(A_2756,'#skF_4',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(A_2756,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),'#skF_4')))
      | ~ v1_funct_2(A_2756,u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(A_2756)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ r1_tarski(A_2756,k2_zfmisc_1('#skF_4',u1_struct_0('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28048,c_30967])).

tff(c_31007,plain,(
    ! [A_2756] :
      ( v5_pre_topc(A_2756,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
      | ~ v5_pre_topc(A_2756,'#skF_1','#skF_2')
      | ~ v1_funct_2(A_2756,'#skF_4','#skF_4')
      | ~ m1_subset_1(A_2756,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),'#skF_4')))
      | ~ v1_funct_2(A_2756,u1_struct_0('#skF_1'),'#skF_4')
      | ~ v1_funct_1(A_2756)
      | ~ r1_tarski(A_2756,k2_zfmisc_1('#skF_4','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28048,c_68,c_66,c_28048,c_28048,c_30989])).

tff(c_27334,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27271,c_84])).

tff(c_27877,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27873,c_27334])).

tff(c_28526,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28039,c_27877])).

tff(c_28489,plain,
    ( r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),k1_zfmisc_1('#skF_4'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_28413,c_191])).

tff(c_28799,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_28489])).

tff(c_28805,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_190,c_28799])).

tff(c_28811,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_28805])).

tff(c_28813,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_28489])).

tff(c_28486,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_28413,c_40])).

tff(c_29516,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28813,c_28486])).

tff(c_29517,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_29516])).

tff(c_29523,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_29517])).

tff(c_29529,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_29523])).

tff(c_29531,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_29516])).

tff(c_28237,plain,(
    ! [D_2481,A_2482,B_2483] :
      ( v5_pre_topc(D_2481,A_2482,g1_pre_topc(u1_struct_0(B_2483),u1_pre_topc(B_2483)))
      | ~ v5_pre_topc(D_2481,A_2482,B_2483)
      | ~ m1_subset_1(D_2481,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2482),u1_struct_0(g1_pre_topc(u1_struct_0(B_2483),u1_pre_topc(B_2483))))))
      | ~ v1_funct_2(D_2481,u1_struct_0(A_2482),u1_struct_0(g1_pre_topc(u1_struct_0(B_2483),u1_pre_topc(B_2483))))
      | ~ m1_subset_1(D_2481,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2482),u1_struct_0(B_2483))))
      | ~ v1_funct_2(D_2481,u1_struct_0(A_2482),u1_struct_0(B_2483))
      | ~ v1_funct_1(D_2481)
      | ~ l1_pre_topc(B_2483)
      | ~ v2_pre_topc(B_2483)
      | ~ l1_pre_topc(A_2482)
      | ~ v2_pre_topc(A_2482) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_28241,plain,(
    ! [A_2482,B_2483] :
      ( v5_pre_topc('#skF_4',A_2482,g1_pre_topc(u1_struct_0(B_2483),u1_pre_topc(B_2483)))
      | ~ v5_pre_topc('#skF_4',A_2482,B_2483)
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_2482),u1_struct_0(g1_pre_topc(u1_struct_0(B_2483),u1_pre_topc(B_2483))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2482),u1_struct_0(B_2483))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_2482),u1_struct_0(B_2483))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(B_2483)
      | ~ v2_pre_topc(B_2483)
      | ~ l1_pre_topc(A_2482)
      | ~ v2_pre_topc(A_2482) ) ),
    inference(resolution,[status(thm)],[c_28070,c_28237])).

tff(c_35583,plain,(
    ! [A_3092,B_3093] :
      ( v5_pre_topc('#skF_4',A_3092,g1_pre_topc(u1_struct_0(B_3093),u1_pre_topc(B_3093)))
      | ~ v5_pre_topc('#skF_4',A_3092,B_3093)
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_3092),u1_struct_0(g1_pre_topc(u1_struct_0(B_3093),u1_pre_topc(B_3093))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_3092),u1_struct_0(B_3093))
      | ~ l1_pre_topc(B_3093)
      | ~ v2_pre_topc(B_3093)
      | ~ l1_pre_topc(A_3092)
      | ~ v2_pre_topc(A_3092) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_28070,c_28241])).

tff(c_35589,plain,(
    ! [B_3093] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0(B_3093),u1_pre_topc(B_3093)))
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_3093)
      | ~ v1_funct_2('#skF_4','#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(B_3093),u1_pre_topc(B_3093))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_3093))
      | ~ l1_pre_topc(B_3093)
      | ~ v2_pre_topc(B_3093)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28413,c_35583])).

tff(c_35711,plain,(
    ! [B_3097] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0(B_3097),u1_pre_topc(B_3097)))
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_3097)
      | ~ l1_pre_topc(B_3097)
      | ~ v2_pre_topc(B_3097) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29531,c_28813,c_28059,c_28413,c_28059,c_35589])).

tff(c_35758,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_28048,c_35711])).

tff(c_35809,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_35758])).

tff(c_35810,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_28526,c_35809])).

tff(c_35815,plain,
    ( ~ v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_4','#skF_4','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),'#skF_4')))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ r1_tarski('#skF_4',k2_zfmisc_1('#skF_4','#skF_4')) ),
    inference(resolution,[status(thm)],[c_31007,c_35810])).

tff(c_35831,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28068,c_58,c_28046,c_28070,c_28059,c_27271,c_35815])).

tff(c_35832,plain,(
    u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_28412])).

tff(c_37927,plain,(
    ! [A_3321,A_3322,B_3323] :
      ( v5_pre_topc(A_3321,A_3322,g1_pre_topc(u1_struct_0(B_3323),u1_pre_topc(B_3323)))
      | ~ v5_pre_topc(A_3321,A_3322,B_3323)
      | ~ v1_funct_2(A_3321,u1_struct_0(A_3322),u1_struct_0(g1_pre_topc(u1_struct_0(B_3323),u1_pre_topc(B_3323))))
      | ~ m1_subset_1(A_3321,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3322),u1_struct_0(B_3323))))
      | ~ v1_funct_2(A_3321,u1_struct_0(A_3322),u1_struct_0(B_3323))
      | ~ v1_funct_1(A_3321)
      | ~ l1_pre_topc(B_3323)
      | ~ v2_pre_topc(B_3323)
      | ~ l1_pre_topc(A_3322)
      | ~ v2_pre_topc(A_3322)
      | ~ r1_tarski(A_3321,k2_zfmisc_1(u1_struct_0(A_3322),u1_struct_0(g1_pre_topc(u1_struct_0(B_3323),u1_pre_topc(B_3323))))) ) ),
    inference(resolution,[status(thm)],[c_12,c_28237])).

tff(c_37955,plain,(
    ! [A_3321,A_3322] :
      ( v5_pre_topc(A_3321,A_3322,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc(A_3321,A_3322,'#skF_2')
      | ~ v1_funct_2(A_3321,u1_struct_0(A_3322),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1(A_3321,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3322),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(A_3321,u1_struct_0(A_3322),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(A_3321)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_3322)
      | ~ v2_pre_topc(A_3322)
      | ~ r1_tarski(A_3321,k2_zfmisc_1(u1_struct_0(A_3322),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28048,c_37927])).

tff(c_42018,plain,(
    ! [A_3692,A_3693] :
      ( v5_pre_topc(A_3692,A_3693,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc(A_3692,A_3693,'#skF_2')
      | ~ m1_subset_1(A_3692,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3693),'#skF_4')))
      | ~ v1_funct_2(A_3692,u1_struct_0(A_3693),'#skF_4')
      | ~ v1_funct_1(A_3692)
      | ~ l1_pre_topc(A_3693)
      | ~ v2_pre_topc(A_3693)
      | ~ r1_tarski(A_3692,k2_zfmisc_1(u1_struct_0(A_3693),'#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35832,c_68,c_66,c_28048,c_28048,c_35832,c_28048,c_28048,c_37955])).

tff(c_42045,plain,(
    ! [A_3693] :
      ( v5_pre_topc('#skF_4',A_3693,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc('#skF_4',A_3693,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_3693),'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(A_3693)
      | ~ v2_pre_topc(A_3693)
      | ~ r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0(A_3693),'#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_28070,c_42018])).

tff(c_42081,plain,(
    ! [A_3694] :
      ( v5_pre_topc('#skF_4',A_3694,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc('#skF_4',A_3694,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_3694),'#skF_4')
      | ~ l1_pre_topc(A_3694)
      | ~ v2_pre_topc(A_3694) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28068,c_58,c_42045])).

tff(c_27884,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27873,c_56])).

tff(c_28047,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28039,c_27884])).

tff(c_35835,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35832,c_28047])).

tff(c_27895,plain,
    ( v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_27873,c_40])).

tff(c_27915,plain,(
    v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_27895])).

tff(c_28042,plain,(
    v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28039,c_27915])).

tff(c_27901,plain,
    ( l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_27873,c_190])).

tff(c_27919,plain,(
    l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_27901])).

tff(c_28044,plain,(
    l1_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28039,c_27919])).

tff(c_38043,plain,(
    ! [A_3337,A_3338,B_3339] :
      ( v5_pre_topc(A_3337,g1_pre_topc(u1_struct_0(A_3338),u1_pre_topc(A_3338)),B_3339)
      | ~ v5_pre_topc(A_3337,A_3338,B_3339)
      | ~ v1_funct_2(A_3337,u1_struct_0(g1_pre_topc(u1_struct_0(A_3338),u1_pre_topc(A_3338))),u1_struct_0(B_3339))
      | ~ m1_subset_1(A_3337,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3338),u1_struct_0(B_3339))))
      | ~ v1_funct_2(A_3337,u1_struct_0(A_3338),u1_struct_0(B_3339))
      | ~ v1_funct_1(A_3337)
      | ~ l1_pre_topc(B_3339)
      | ~ v2_pre_topc(B_3339)
      | ~ l1_pre_topc(A_3338)
      | ~ v2_pre_topc(A_3338)
      | ~ r1_tarski(A_3337,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_3338),u1_pre_topc(A_3338))),u1_struct_0(B_3339))) ) ),
    inference(resolution,[status(thm)],[c_12,c_28149])).

tff(c_38065,plain,(
    ! [A_3337,A_3338] :
      ( v5_pre_topc(A_3337,g1_pre_topc(u1_struct_0(A_3338),u1_pre_topc(A_3338)),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc(A_3337,A_3338,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v1_funct_2(A_3337,u1_struct_0(g1_pre_topc(u1_struct_0(A_3338),u1_pre_topc(A_3338))),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1(A_3337,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3338),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))))
      | ~ v1_funct_2(A_3337,u1_struct_0(A_3338),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
      | ~ v1_funct_1(A_3337)
      | ~ l1_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_3338)
      | ~ v2_pre_topc(A_3338)
      | ~ r1_tarski(A_3337,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_3338),u1_pre_topc(A_3338))),'#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35832,c_38043])).

tff(c_38157,plain,(
    ! [A_3345,A_3346] :
      ( v5_pre_topc(A_3345,g1_pre_topc(u1_struct_0(A_3346),u1_pre_topc(A_3346)),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc(A_3345,A_3346,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v1_funct_2(A_3345,u1_struct_0(g1_pre_topc(u1_struct_0(A_3346),u1_pre_topc(A_3346))),'#skF_4')
      | ~ m1_subset_1(A_3345,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3346),'#skF_4')))
      | ~ v1_funct_2(A_3345,u1_struct_0(A_3346),'#skF_4')
      | ~ v1_funct_1(A_3345)
      | ~ l1_pre_topc(A_3346)
      | ~ v2_pre_topc(A_3346)
      | ~ r1_tarski(A_3345,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_3346),u1_pre_topc(A_3346))),'#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28042,c_28044,c_35832,c_35832,c_35832,c_38065])).

tff(c_35947,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28039,c_27877])).

tff(c_38167,plain,
    ( ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),'#skF_4')))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_38157,c_35947])).

tff(c_38183,plain,(
    ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28068,c_72,c_70,c_58,c_28046,c_28070,c_35835,c_38167])).

tff(c_42102,plain,
    ( ~ v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42081,c_38183])).

tff(c_42143,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_28046,c_27271,c_42102])).

tff(c_42144,plain,(
    u1_struct_0('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_27520])).

tff(c_42159,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42144,c_81])).

tff(c_42158,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42144,c_56])).

tff(c_27312,plain,(
    ! [A_2415,B_2416,A_2417] :
      ( k1_relset_1(A_2415,B_2416,A_2417) = k1_relat_1(A_2417)
      | ~ r1_tarski(A_2417,k2_zfmisc_1(A_2415,B_2416)) ) ),
    inference(resolution,[status(thm)],[c_12,c_27282])).

tff(c_27327,plain,(
    k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_152,c_27312])).

tff(c_42720,plain,(
    k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42144,c_27327])).

tff(c_42154,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42144,c_152])).

tff(c_42338,plain,(
    ! [B_3703,A_3704,C_3705] :
      ( k1_xboole_0 = B_3703
      | k1_relset_1(A_3704,B_3703,C_3705) = A_3704
      | ~ v1_funct_2(C_3705,A_3704,B_3703)
      | ~ m1_subset_1(C_3705,k1_zfmisc_1(k2_zfmisc_1(A_3704,B_3703))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_43101,plain,(
    ! [B_3796,A_3797,A_3798] :
      ( k1_xboole_0 = B_3796
      | k1_relset_1(A_3797,B_3796,A_3798) = A_3797
      | ~ v1_funct_2(A_3798,A_3797,B_3796)
      | ~ r1_tarski(A_3798,k2_zfmisc_1(A_3797,B_3796)) ) ),
    inference(resolution,[status(thm)],[c_12,c_42338])).

tff(c_43116,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0
    | k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') = u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(resolution,[status(thm)],[c_42154,c_43101])).

tff(c_43133,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42158,c_42720,c_43116])).

tff(c_43151,plain,(
    u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_43133])).

tff(c_42157,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42144,c_85])).

tff(c_42151,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42144,c_27334])).

tff(c_42170,plain,
    ( v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_42144,c_40])).

tff(c_42190,plain,(
    v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_42170])).

tff(c_42176,plain,
    ( l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_42144,c_190])).

tff(c_42194,plain,(
    l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_42176])).

tff(c_42155,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42144,c_54])).

tff(c_42659,plain,(
    ! [D_3739,A_3740,B_3741] :
      ( v5_pre_topc(D_3739,A_3740,g1_pre_topc(u1_struct_0(B_3741),u1_pre_topc(B_3741)))
      | ~ v5_pre_topc(D_3739,A_3740,B_3741)
      | ~ m1_subset_1(D_3739,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3740),u1_struct_0(g1_pre_topc(u1_struct_0(B_3741),u1_pre_topc(B_3741))))))
      | ~ v1_funct_2(D_3739,u1_struct_0(A_3740),u1_struct_0(g1_pre_topc(u1_struct_0(B_3741),u1_pre_topc(B_3741))))
      | ~ m1_subset_1(D_3739,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3740),u1_struct_0(B_3741))))
      | ~ v1_funct_2(D_3739,u1_struct_0(A_3740),u1_struct_0(B_3741))
      | ~ v1_funct_1(D_3739)
      | ~ l1_pre_topc(B_3741)
      | ~ v2_pre_topc(B_3741)
      | ~ l1_pre_topc(A_3740)
      | ~ v2_pre_topc(A_3740) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_42662,plain,
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
    inference(resolution,[status(thm)],[c_42155,c_42659])).

tff(c_42686,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42190,c_42194,c_68,c_66,c_58,c_42158,c_42662])).

tff(c_42687,plain,
    ( ~ v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_42151,c_42686])).

tff(c_44099,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42159,c_43151,c_42157,c_43151,c_42687])).

tff(c_42156,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42144,c_121])).

tff(c_42534,plain,(
    ! [D_3724,A_3725,B_3726] :
      ( v5_pre_topc(D_3724,g1_pre_topc(u1_struct_0(A_3725),u1_pre_topc(A_3725)),B_3726)
      | ~ v5_pre_topc(D_3724,A_3725,B_3726)
      | ~ m1_subset_1(D_3724,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_3725),u1_pre_topc(A_3725))),u1_struct_0(B_3726))))
      | ~ v1_funct_2(D_3724,u1_struct_0(g1_pre_topc(u1_struct_0(A_3725),u1_pre_topc(A_3725))),u1_struct_0(B_3726))
      | ~ m1_subset_1(D_3724,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3725),u1_struct_0(B_3726))))
      | ~ v1_funct_2(D_3724,u1_struct_0(A_3725),u1_struct_0(B_3726))
      | ~ v1_funct_1(D_3724)
      | ~ l1_pre_topc(B_3726)
      | ~ v2_pre_topc(B_3726)
      | ~ l1_pre_topc(A_3725)
      | ~ v2_pre_topc(A_3725) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_44487,plain,(
    ! [A_3942,A_3943,B_3944] :
      ( v5_pre_topc(A_3942,g1_pre_topc(u1_struct_0(A_3943),u1_pre_topc(A_3943)),B_3944)
      | ~ v5_pre_topc(A_3942,A_3943,B_3944)
      | ~ v1_funct_2(A_3942,u1_struct_0(g1_pre_topc(u1_struct_0(A_3943),u1_pre_topc(A_3943))),u1_struct_0(B_3944))
      | ~ m1_subset_1(A_3942,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3943),u1_struct_0(B_3944))))
      | ~ v1_funct_2(A_3942,u1_struct_0(A_3943),u1_struct_0(B_3944))
      | ~ v1_funct_1(A_3942)
      | ~ l1_pre_topc(B_3944)
      | ~ v2_pre_topc(B_3944)
      | ~ l1_pre_topc(A_3943)
      | ~ v2_pre_topc(A_3943)
      | ~ r1_tarski(A_3942,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_3943),u1_pre_topc(A_3943))),u1_struct_0(B_3944))) ) ),
    inference(resolution,[status(thm)],[c_12,c_42534])).

tff(c_44520,plain,(
    ! [A_3942,B_3944] :
      ( v5_pre_topc(A_3942,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_3944)
      | ~ v5_pre_topc(A_3942,'#skF_1',B_3944)
      | ~ v1_funct_2(A_3942,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_3944))
      | ~ m1_subset_1(A_3942,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_3944))))
      | ~ v1_funct_2(A_3942,u1_struct_0('#skF_1'),u1_struct_0(B_3944))
      | ~ v1_funct_1(A_3942)
      | ~ l1_pre_topc(B_3944)
      | ~ v2_pre_topc(B_3944)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r1_tarski(A_3942,k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(B_3944))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42144,c_44487])).

tff(c_49851,plain,(
    ! [A_4401,B_4402] :
      ( v5_pre_topc(A_4401,g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),B_4402)
      | ~ v5_pre_topc(A_4401,'#skF_1',B_4402)
      | ~ m1_subset_1(A_4401,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_4402))))
      | ~ v1_funct_2(A_4401,k1_relat_1('#skF_4'),u1_struct_0(B_4402))
      | ~ v1_funct_1(A_4401)
      | ~ l1_pre_topc(B_4402)
      | ~ v2_pre_topc(B_4402)
      | ~ r1_tarski(A_4401,k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_4402))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43151,c_72,c_70,c_42144,c_42144,c_43151,c_42144,c_42144,c_44520])).

tff(c_49880,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | ~ r1_tarski('#skF_4',k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_42157,c_49851])).

tff(c_49919,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42156,c_68,c_66,c_58,c_42159,c_27271,c_49880])).

tff(c_49921,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44099,c_49919])).

tff(c_49922,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_43133])).

tff(c_49946,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49922,c_42158])).

tff(c_49945,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49922,c_42155])).

tff(c_22,plain,(
    ! [C_17,A_15] :
      ( k1_xboole_0 = C_17
      | ~ v1_funct_2(C_17,A_15,k1_xboole_0)
      | k1_xboole_0 = A_15
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_50043,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),k1_xboole_0)
    | u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_49945,c_22])).

tff(c_50062,plain,
    ( k1_xboole_0 = '#skF_4'
    | u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_49946,c_50043])).

tff(c_50066,plain,(
    u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_50062])).

tff(c_49923,plain,(
    u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) != k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_43133])).

tff(c_50069,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50066,c_49923])).

tff(c_27395,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))) ),
    inference(superposition,[status(thm),theory(equality)],[c_27297,c_16])).

tff(c_27405,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_27395])).

tff(c_42393,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42144,c_27405])).

tff(c_42400,plain,(
    r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))) ),
    inference(resolution,[status(thm)],[c_42393,c_10])).

tff(c_50071,plain,(
    r1_tarski(k1_relat_1('#skF_4'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50066,c_42400])).

tff(c_50159,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50071,c_113])).

tff(c_50165,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50069,c_50159])).

tff(c_50166,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_50062])).

tff(c_50200,plain,(
    ! [B_2431] : v1_funct_2('#skF_4','#skF_4',B_2431) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50166,c_50166,c_27541])).

tff(c_50204,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50166,c_50166,c_27456])).

tff(c_50238,plain,(
    u1_struct_0('#skF_1') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50204,c_42144])).

tff(c_42683,plain,(
    ! [A_3740,B_3741] :
      ( v5_pre_topc(k1_xboole_0,A_3740,g1_pre_topc(u1_struct_0(B_3741),u1_pre_topc(B_3741)))
      | ~ v5_pre_topc(k1_xboole_0,A_3740,B_3741)
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(A_3740),u1_struct_0(g1_pre_topc(u1_struct_0(B_3741),u1_pre_topc(B_3741))))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3740),u1_struct_0(B_3741))))
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(A_3740),u1_struct_0(B_3741))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ l1_pre_topc(B_3741)
      | ~ v2_pre_topc(B_3741)
      | ~ l1_pre_topc(A_3740)
      | ~ v2_pre_topc(A_3740) ) ),
    inference(resolution,[status(thm)],[c_8,c_42659])).

tff(c_42696,plain,(
    ! [A_3740,B_3741] :
      ( v5_pre_topc(k1_xboole_0,A_3740,g1_pre_topc(u1_struct_0(B_3741),u1_pre_topc(B_3741)))
      | ~ v5_pre_topc(k1_xboole_0,A_3740,B_3741)
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(A_3740),u1_struct_0(g1_pre_topc(u1_struct_0(B_3741),u1_pre_topc(B_3741))))
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(A_3740),u1_struct_0(B_3741))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ l1_pre_topc(B_3741)
      | ~ v2_pre_topc(B_3741)
      | ~ l1_pre_topc(A_3740)
      | ~ v2_pre_topc(A_3740) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_42683])).

tff(c_50652,plain,(
    ! [A_4439,B_4440] :
      ( v5_pre_topc('#skF_4',A_4439,g1_pre_topc(u1_struct_0(B_4440),u1_pre_topc(B_4440)))
      | ~ v5_pre_topc('#skF_4',A_4439,B_4440)
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_4439),u1_struct_0(g1_pre_topc(u1_struct_0(B_4440),u1_pre_topc(B_4440))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_4439),u1_struct_0(B_4440))
      | ~ l1_pre_topc(B_4440)
      | ~ v2_pre_topc(B_4440)
      | ~ l1_pre_topc(A_4439)
      | ~ v2_pre_topc(A_4439) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_50166,c_50166,c_50166,c_50166,c_50166,c_42696])).

tff(c_50655,plain,(
    ! [B_4440] :
      ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0(B_4440),u1_pre_topc(B_4440)))
      | ~ v5_pre_topc('#skF_4','#skF_1',B_4440)
      | ~ v1_funct_2('#skF_4','#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(B_4440),u1_pre_topc(B_4440))))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0(B_4440))
      | ~ l1_pre_topc(B_4440)
      | ~ v2_pre_topc(B_4440)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50238,c_50652])).

tff(c_50663,plain,(
    ! [B_4440] :
      ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0(B_4440),u1_pre_topc(B_4440)))
      | ~ v5_pre_topc('#skF_4','#skF_1',B_4440)
      | ~ l1_pre_topc(B_4440)
      | ~ v2_pre_topc(B_4440) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_50200,c_50238,c_50200,c_50655])).

tff(c_50219,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50204,c_42151])).

tff(c_36,plain,(
    ! [A_19,B_20] :
      ( v1_pre_topc(g1_pre_topc(A_19,B_20))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(k1_zfmisc_1(A_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_189,plain,(
    ! [A_84] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_84),u1_pre_topc(A_84)))
      | ~ l1_pre_topc(A_84) ) ),
    inference(resolution,[status(thm)],[c_179,c_36])).

tff(c_50004,plain,
    ( v1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_49922,c_189])).

tff(c_51157,plain,
    ( v1_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50166,c_50004])).

tff(c_51158,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_51157])).

tff(c_51218,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_190,c_51158])).

tff(c_51224,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_51218])).

tff(c_51226,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_51157])).

tff(c_49995,plain,
    ( v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_49922,c_40])).

tff(c_52256,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51226,c_50166,c_49995])).

tff(c_52257,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_52256])).

tff(c_52263,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_52257])).

tff(c_52269,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_52263])).

tff(c_52271,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_52256])).

tff(c_50180,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50166,c_49946])).

tff(c_50628,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50204,c_50180])).

tff(c_50181,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50166,c_49922])).

tff(c_42555,plain,(
    ! [A_3725,B_3726] :
      ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(A_3725),u1_pre_topc(A_3725)),B_3726)
      | ~ v5_pre_topc(k1_xboole_0,A_3725,B_3726)
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(A_3725),u1_pre_topc(A_3725))),u1_struct_0(B_3726))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3725),u1_struct_0(B_3726))))
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(A_3725),u1_struct_0(B_3726))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ l1_pre_topc(B_3726)
      | ~ v2_pre_topc(B_3726)
      | ~ l1_pre_topc(A_3725)
      | ~ v2_pre_topc(A_3725) ) ),
    inference(resolution,[status(thm)],[c_8,c_42534])).

tff(c_42564,plain,(
    ! [A_3725,B_3726] :
      ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(A_3725),u1_pre_topc(A_3725)),B_3726)
      | ~ v5_pre_topc(k1_xboole_0,A_3725,B_3726)
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(A_3725),u1_pre_topc(A_3725))),u1_struct_0(B_3726))
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(A_3725),u1_struct_0(B_3726))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ l1_pre_topc(B_3726)
      | ~ v2_pre_topc(B_3726)
      | ~ l1_pre_topc(A_3725)
      | ~ v2_pre_topc(A_3725) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_42555])).

tff(c_50772,plain,(
    ! [A_4442,B_4443] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_4442),u1_pre_topc(A_4442)),B_4443)
      | ~ v5_pre_topc('#skF_4',A_4442,B_4443)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_4442),u1_pre_topc(A_4442))),u1_struct_0(B_4443))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_4442),u1_struct_0(B_4443))
      | ~ l1_pre_topc(B_4443)
      | ~ v2_pre_topc(B_4443)
      | ~ l1_pre_topc(A_4442)
      | ~ v2_pre_topc(A_4442) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_50166,c_50166,c_50166,c_50166,c_50166,c_42564])).

tff(c_50784,plain,(
    ! [B_4443] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_4443)
      | ~ v5_pre_topc('#skF_4','#skF_1',B_4443)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),u1_struct_0(B_4443))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0(B_4443))
      | ~ l1_pre_topc(B_4443)
      | ~ v2_pre_topc(B_4443)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50238,c_50772])).

tff(c_53650,plain,(
    ! [B_4684] :
      ( v5_pre_topc('#skF_4',g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),B_4684)
      | ~ v5_pre_topc('#skF_4','#skF_1',B_4684)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),u1_struct_0(B_4684))
      | ~ l1_pre_topc(B_4684)
      | ~ v2_pre_topc(B_4684) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_50200,c_50238,c_50238,c_50784])).

tff(c_53656,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),'#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_50181,c_53650])).

tff(c_53662,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52271,c_51226,c_50628,c_53656])).

tff(c_53663,plain,(
    ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50219,c_53662])).

tff(c_53669,plain,
    ( ~ v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50663,c_53663])).

tff(c_53676,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_27271,c_53669])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:57:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 23.80/13.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 24.01/13.58  
% 24.01/13.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 24.01/13.58  %$ v5_pre_topc > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_pre_topc > k1_relset_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 24.01/13.58  
% 24.01/13.58  %Foreground sorts:
% 24.01/13.58  
% 24.01/13.58  
% 24.01/13.58  %Background operators:
% 24.01/13.58  
% 24.01/13.58  
% 24.01/13.58  %Foreground operators:
% 24.01/13.58  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 24.01/13.58  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 24.01/13.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 24.01/13.58  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 24.01/13.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 24.01/13.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 24.01/13.58  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 24.01/13.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 24.01/13.58  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 24.01/13.58  tff('#skF_2', type, '#skF_2': $i).
% 24.01/13.58  tff('#skF_3', type, '#skF_3': $i).
% 24.01/13.58  tff('#skF_1', type, '#skF_1': $i).
% 24.01/13.58  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 24.01/13.58  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 24.01/13.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 24.01/13.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 24.01/13.58  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 24.01/13.58  tff('#skF_4', type, '#skF_4': $i).
% 24.01/13.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 24.01/13.58  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 24.01/13.58  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 24.01/13.58  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 24.01/13.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 24.01/13.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 24.01/13.58  
% 24.36/13.63  tff(f_181, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))), u1_struct_0(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))), u1_struct_0(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))) => ((C = D) => (v5_pre_topc(C, A, B) <=> v5_pre_topc(D, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)), g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_pre_topc)).
% 24.36/13.63  tff(f_93, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & v2_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_pre_topc)).
% 24.36/13.63  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 24.36/13.63  tff(f_81, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v1_pre_topc(g1_pre_topc(A, B)) & l1_pre_topc(g1_pre_topc(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 24.36/13.63  tff(f_33, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 24.36/13.63  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 24.36/13.63  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 24.36/13.63  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 24.36/13.63  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 24.36/13.63  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 24.36/13.63  tff(f_122, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))), u1_struct_0(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))), u1_struct_0(B))))) => ((C = D) => (v5_pre_topc(C, A, B) <=> v5_pre_topc(D, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)), B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_pre_topc)).
% 24.36/13.63  tff(f_151, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(A), u1_struct_0(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))) => ((C = D) => (v5_pre_topc(C, A, B) <=> v5_pre_topc(D, A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_pre_topc)).
% 24.36/13.63  tff(c_68, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_181])).
% 24.36/13.63  tff(c_66, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_181])).
% 24.36/13.63  tff(c_52, plain, ('#skF_3'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_181])).
% 24.36/13.63  tff(c_80, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_181])).
% 24.36/13.63  tff(c_82, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_80])).
% 24.36/13.63  tff(c_290, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_82])).
% 24.36/13.63  tff(c_74, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_181])).
% 24.36/13.63  tff(c_84, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_74])).
% 24.36/13.63  tff(c_343, plain, (~v5_pre_topc('#skF_4', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_290, c_84])).
% 24.36/13.63  tff(c_40, plain, (![A_22]: (v2_pre_topc(g1_pre_topc(u1_struct_0(A_22), u1_pre_topc(A_22))) | ~l1_pre_topc(A_22) | ~v2_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_93])).
% 24.36/13.63  tff(c_179, plain, (![A_84]: (m1_subset_1(u1_pre_topc(A_84), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_84)))) | ~l1_pre_topc(A_84))), inference(cnfTransformation, [status(thm)], [f_85])).
% 24.36/13.63  tff(c_34, plain, (![A_19, B_20]: (l1_pre_topc(g1_pre_topc(A_19, B_20)) | ~m1_subset_1(B_20, k1_zfmisc_1(k1_zfmisc_1(A_19))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 24.36/13.63  tff(c_190, plain, (![A_84]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_84), u1_pre_topc(A_84))) | ~l1_pre_topc(A_84))), inference(resolution, [status(thm)], [c_179, c_34])).
% 24.36/13.63  tff(c_72, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_181])).
% 24.36/13.63  tff(c_70, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_181])).
% 24.36/13.63  tff(c_8, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 24.36/13.63  tff(c_97, plain, (![A_67, B_68]: (r1_tarski(A_67, B_68) | ~m1_subset_1(A_67, k1_zfmisc_1(B_68)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 24.36/13.63  tff(c_101, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(resolution, [status(thm)], [c_8, c_97])).
% 24.36/13.63  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 24.36/13.63  tff(c_62, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_181])).
% 24.36/13.63  tff(c_81, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_62])).
% 24.36/13.63  tff(c_60, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_181])).
% 24.36/13.63  tff(c_85, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_60])).
% 24.36/13.63  tff(c_300, plain, (![A_106, B_107, C_108]: (k1_relset_1(A_106, B_107, C_108)=k1_relat_1(C_108) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 24.36/13.63  tff(c_316, plain, (k1_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_85, c_300])).
% 24.36/13.63  tff(c_807, plain, (![B_155, A_156, C_157]: (k1_xboole_0=B_155 | k1_relset_1(A_156, B_155, C_157)=A_156 | ~v1_funct_2(C_157, A_156, B_155) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_156, B_155))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 24.36/13.63  tff(c_817, plain, (u1_struct_0('#skF_2')=k1_xboole_0 | k1_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4')=u1_struct_0('#skF_1') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_85, c_807])).
% 24.36/13.63  tff(c_832, plain, (u1_struct_0('#skF_2')=k1_xboole_0 | u1_struct_0('#skF_1')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_316, c_817])).
% 24.36/13.63  tff(c_836, plain, (u1_struct_0('#skF_1')=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_832])).
% 24.36/13.63  tff(c_374, plain, (![A_116, B_117, C_118]: (m1_subset_1(k1_relset_1(A_116, B_117, C_118), k1_zfmisc_1(A_116)) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 24.36/13.63  tff(c_397, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_316, c_374])).
% 24.36/13.63  tff(c_407, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_397])).
% 24.36/13.63  tff(c_10, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 24.36/13.63  tff(c_524, plain, (r1_tarski(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_407, c_10])).
% 24.36/13.63  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 24.36/13.63  tff(c_527, plain, (u1_struct_0('#skF_1')=k1_relat_1('#skF_4') | ~r1_tarski(u1_struct_0('#skF_1'), k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_524, c_2])).
% 24.36/13.63  tff(c_544, plain, (~r1_tarski(u1_struct_0('#skF_1'), k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_527])).
% 24.36/13.63  tff(c_840, plain, (~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_836, c_544])).
% 24.36/13.63  tff(c_857, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_840])).
% 24.36/13.63  tff(c_858, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_832])).
% 24.36/13.63  tff(c_870, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_858, c_81])).
% 24.36/13.63  tff(c_121, plain, (r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_85, c_10])).
% 24.36/13.63  tff(c_867, plain, (r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0('#skF_1'), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_858, c_121])).
% 24.36/13.63  tff(c_12, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 24.36/13.63  tff(c_501, plain, (![C_123, A_124]: (k1_xboole_0=C_123 | ~v1_funct_2(C_123, A_124, k1_xboole_0) | k1_xboole_0=A_124 | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_124, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 24.36/13.63  tff(c_515, plain, (![A_4, A_124]: (k1_xboole_0=A_4 | ~v1_funct_2(A_4, A_124, k1_xboole_0) | k1_xboole_0=A_124 | ~r1_tarski(A_4, k2_zfmisc_1(A_124, k1_xboole_0)))), inference(resolution, [status(thm)], [c_12, c_501])).
% 24.36/13.63  tff(c_947, plain, (k1_xboole_0='#skF_4' | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), k1_xboole_0) | u1_struct_0('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_867, c_515])).
% 24.36/13.63  tff(c_955, plain, (k1_xboole_0='#skF_4' | u1_struct_0('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_870, c_947])).
% 24.36/13.63  tff(c_958, plain, (u1_struct_0('#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_955])).
% 24.36/13.63  tff(c_997, plain, (~r1_tarski(k1_xboole_0, k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_958, c_544])).
% 24.36/13.63  tff(c_1003, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_101, c_997])).
% 24.36/13.63  tff(c_1004, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_955])).
% 24.36/13.63  tff(c_1012, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1004, c_870])).
% 24.36/13.63  tff(c_1031, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_1004, c_101])).
% 24.36/13.63  tff(c_58, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_181])).
% 24.36/13.63  tff(c_1033, plain, (![A_3]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_1004, c_8])).
% 24.36/13.63  tff(c_318, plain, (![A_106, B_107]: (k1_relset_1(A_106, B_107, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_300])).
% 24.36/13.63  tff(c_400, plain, (![A_106, B_107]: (m1_subset_1(k1_relat_1(k1_xboole_0), k1_zfmisc_1(A_106)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))))), inference(superposition, [status(thm), theory('equality')], [c_318, c_374])).
% 24.36/13.63  tff(c_410, plain, (![A_119]: (m1_subset_1(k1_relat_1(k1_xboole_0), k1_zfmisc_1(A_119)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_400])).
% 24.36/13.63  tff(c_433, plain, (![A_120]: (r1_tarski(k1_relat_1(k1_xboole_0), A_120))), inference(resolution, [status(thm)], [c_410, c_10])).
% 24.36/13.63  tff(c_108, plain, (![B_72, A_73]: (B_72=A_73 | ~r1_tarski(B_72, A_73) | ~r1_tarski(A_73, B_72))), inference(cnfTransformation, [status(thm)], [f_31])).
% 24.36/13.63  tff(c_113, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_101, c_108])).
% 24.36/13.63  tff(c_455, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_433, c_113])).
% 24.36/13.63  tff(c_459, plain, (![A_106, B_107]: (k1_relset_1(A_106, B_107, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_455, c_318])).
% 24.36/13.63  tff(c_684, plain, (![C_140, B_141]: (v1_funct_2(C_140, k1_xboole_0, B_141) | k1_relset_1(k1_xboole_0, B_141, C_140)!=k1_xboole_0 | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_141))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 24.36/13.63  tff(c_696, plain, (![B_141]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_141) | k1_relset_1(k1_xboole_0, B_141, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_684])).
% 24.36/13.63  tff(c_701, plain, (![B_141]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_141))), inference(demodulation, [status(thm), theory('equality')], [c_459, c_696])).
% 24.36/13.63  tff(c_1020, plain, (![B_141]: (v1_funct_2('#skF_4', '#skF_4', B_141))), inference(demodulation, [status(thm), theory('equality')], [c_1004, c_1004, c_701])).
% 24.36/13.63  tff(c_1026, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1004, c_1004, c_455])).
% 24.36/13.63  tff(c_1014, plain, (u1_struct_0('#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1004, c_858])).
% 24.36/13.63  tff(c_56, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_181])).
% 24.36/13.63  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))))), inference(cnfTransformation, [status(thm)], [f_181])).
% 24.36/13.63  tff(c_315, plain, (k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_300])).
% 24.36/13.63  tff(c_814, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0 | k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')=u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(resolution, [status(thm)], [c_54, c_807])).
% 24.36/13.63  tff(c_829, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0 | u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_315, c_814])).
% 24.36/13.63  tff(c_1386, plain, (u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))='#skF_4' | u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1026, c_1014, c_1004, c_829])).
% 24.36/13.63  tff(c_1387, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))='#skF_4'), inference(splitLeft, [status(thm)], [c_1386])).
% 24.36/13.63  tff(c_1309, plain, (![D_177, A_178, B_179]: (v5_pre_topc(D_177, A_178, B_179) | ~v5_pre_topc(D_177, g1_pre_topc(u1_struct_0(A_178), u1_pre_topc(A_178)), B_179) | ~m1_subset_1(D_177, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_178), u1_pre_topc(A_178))), u1_struct_0(B_179)))) | ~v1_funct_2(D_177, u1_struct_0(g1_pre_topc(u1_struct_0(A_178), u1_pre_topc(A_178))), u1_struct_0(B_179)) | ~m1_subset_1(D_177, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_178), u1_struct_0(B_179)))) | ~v1_funct_2(D_177, u1_struct_0(A_178), u1_struct_0(B_179)) | ~v1_funct_1(D_177) | ~l1_pre_topc(B_179) | ~v2_pre_topc(B_179) | ~l1_pre_topc(A_178) | ~v2_pre_topc(A_178))), inference(cnfTransformation, [status(thm)], [f_122])).
% 24.36/13.63  tff(c_1313, plain, (![A_178, B_179]: (v5_pre_topc('#skF_4', A_178, B_179) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_178), u1_pre_topc(A_178)), B_179) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_178), u1_pre_topc(A_178))), u1_struct_0(B_179)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_178), u1_struct_0(B_179)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_178), u1_struct_0(B_179)) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(B_179) | ~v2_pre_topc(B_179) | ~l1_pre_topc(A_178) | ~v2_pre_topc(A_178))), inference(resolution, [status(thm)], [c_1033, c_1309])).
% 24.36/13.63  tff(c_8079, plain, (![A_773, B_774]: (v5_pre_topc('#skF_4', A_773, B_774) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_773), u1_pre_topc(A_773)), B_774) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_773), u1_pre_topc(A_773))), u1_struct_0(B_774)) | ~v1_funct_2('#skF_4', u1_struct_0(A_773), u1_struct_0(B_774)) | ~l1_pre_topc(B_774) | ~v2_pre_topc(B_774) | ~l1_pre_topc(A_773) | ~v2_pre_topc(A_773))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1033, c_1313])).
% 24.36/13.63  tff(c_8097, plain, (![A_773]: (v5_pre_topc('#skF_4', A_773, '#skF_2') | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_773), u1_pre_topc(A_773)), '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_773), u1_pre_topc(A_773))), '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0(A_773), u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(A_773) | ~v2_pre_topc(A_773))), inference(superposition, [status(thm), theory('equality')], [c_1014, c_8079])).
% 24.36/13.63  tff(c_8404, plain, (![A_784]: (v5_pre_topc('#skF_4', A_784, '#skF_2') | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_784), u1_pre_topc(A_784)), '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_784), u1_pre_topc(A_784))), '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0(A_784), '#skF_4') | ~l1_pre_topc(A_784) | ~v2_pre_topc(A_784))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_1014, c_8097])).
% 24.36/13.63  tff(c_8413, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~v1_funct_2('#skF_4', '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1387, c_8404])).
% 24.36/13.63  tff(c_8428, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_1012, c_1020, c_8413])).
% 24.36/13.63  tff(c_8429, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_343, c_8428])).
% 24.36/13.63  tff(c_862, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_858, c_290])).
% 24.36/13.63  tff(c_1532, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1004, c_862])).
% 24.36/13.63  tff(c_1468, plain, (l1_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_1387, c_190])).
% 24.36/13.63  tff(c_1895, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_1468])).
% 24.36/13.63  tff(c_1901, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_190, c_1895])).
% 24.36/13.63  tff(c_1907, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_1901])).
% 24.36/13.63  tff(c_1909, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_1468])).
% 24.36/13.63  tff(c_1462, plain, (v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_1387, c_40])).
% 24.36/13.63  tff(c_2560, plain, (v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1909, c_1462])).
% 24.36/13.63  tff(c_2561, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_2560])).
% 24.36/13.63  tff(c_2567, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_2561])).
% 24.36/13.63  tff(c_2573, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_2567])).
% 24.36/13.63  tff(c_2575, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_2560])).
% 24.36/13.63  tff(c_1183, plain, (![D_168, A_169, B_170]: (v5_pre_topc(D_168, A_169, B_170) | ~v5_pre_topc(D_168, A_169, g1_pre_topc(u1_struct_0(B_170), u1_pre_topc(B_170))) | ~m1_subset_1(D_168, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_169), u1_struct_0(g1_pre_topc(u1_struct_0(B_170), u1_pre_topc(B_170)))))) | ~v1_funct_2(D_168, u1_struct_0(A_169), u1_struct_0(g1_pre_topc(u1_struct_0(B_170), u1_pre_topc(B_170)))) | ~m1_subset_1(D_168, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_169), u1_struct_0(B_170)))) | ~v1_funct_2(D_168, u1_struct_0(A_169), u1_struct_0(B_170)) | ~v1_funct_1(D_168) | ~l1_pre_topc(B_170) | ~v2_pre_topc(B_170) | ~l1_pre_topc(A_169) | ~v2_pre_topc(A_169))), inference(cnfTransformation, [status(thm)], [f_151])).
% 24.36/13.63  tff(c_1187, plain, (![A_169, B_170]: (v5_pre_topc('#skF_4', A_169, B_170) | ~v5_pre_topc('#skF_4', A_169, g1_pre_topc(u1_struct_0(B_170), u1_pre_topc(B_170))) | ~v1_funct_2('#skF_4', u1_struct_0(A_169), u1_struct_0(g1_pre_topc(u1_struct_0(B_170), u1_pre_topc(B_170)))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_169), u1_struct_0(B_170)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_169), u1_struct_0(B_170)) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(B_170) | ~v2_pre_topc(B_170) | ~l1_pre_topc(A_169) | ~v2_pre_topc(A_169))), inference(resolution, [status(thm)], [c_1033, c_1183])).
% 24.36/13.63  tff(c_9435, plain, (![A_814, B_815]: (v5_pre_topc('#skF_4', A_814, B_815) | ~v5_pre_topc('#skF_4', A_814, g1_pre_topc(u1_struct_0(B_815), u1_pre_topc(B_815))) | ~v1_funct_2('#skF_4', u1_struct_0(A_814), u1_struct_0(g1_pre_topc(u1_struct_0(B_815), u1_pre_topc(B_815)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_814), u1_struct_0(B_815)) | ~l1_pre_topc(B_815) | ~v2_pre_topc(B_815) | ~l1_pre_topc(A_814) | ~v2_pre_topc(A_814))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1033, c_1187])).
% 24.36/13.63  tff(c_9441, plain, (![B_815]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_815) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0(B_815), u1_pre_topc(B_815))) | ~v1_funct_2('#skF_4', '#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(B_815), u1_pre_topc(B_815)))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_815)) | ~l1_pre_topc(B_815) | ~v2_pre_topc(B_815) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_1387, c_9435])).
% 24.36/13.63  tff(c_9524, plain, (![B_817]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_817) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0(B_817), u1_pre_topc(B_817))) | ~l1_pre_topc(B_817) | ~v2_pre_topc(B_817))), inference(demodulation, [status(thm), theory('equality')], [c_2575, c_1909, c_1020, c_1387, c_1020, c_9441])).
% 24.36/13.63  tff(c_9575, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1014, c_9524])).
% 24.36/13.63  tff(c_9624, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_1532, c_9575])).
% 24.36/13.63  tff(c_9626, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8429, c_9624])).
% 24.36/13.63  tff(c_9627, plain, (u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))='#skF_4'), inference(splitRight, [status(thm)], [c_1386])).
% 24.36/13.63  tff(c_869, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_858, c_56])).
% 24.36/13.63  tff(c_1013, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_1004, c_869])).
% 24.36/13.63  tff(c_9630, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9627, c_1013])).
% 24.36/13.63  tff(c_9782, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1004, c_862])).
% 24.36/13.63  tff(c_880, plain, (v2_pre_topc(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_858, c_40])).
% 24.36/13.63  tff(c_900, plain, (v2_pre_topc(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_880])).
% 24.36/13.63  tff(c_1009, plain, (v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1004, c_900])).
% 24.36/13.63  tff(c_886, plain, (l1_pre_topc(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_858, c_190])).
% 24.36/13.63  tff(c_904, plain, (l1_pre_topc(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_886])).
% 24.36/13.63  tff(c_1010, plain, (l1_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1004, c_904])).
% 24.36/13.63  tff(c_11211, plain, (![A_998, A_999, B_1000]: (v5_pre_topc(A_998, A_999, B_1000) | ~v5_pre_topc(A_998, g1_pre_topc(u1_struct_0(A_999), u1_pre_topc(A_999)), B_1000) | ~v1_funct_2(A_998, u1_struct_0(g1_pre_topc(u1_struct_0(A_999), u1_pre_topc(A_999))), u1_struct_0(B_1000)) | ~m1_subset_1(A_998, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_999), u1_struct_0(B_1000)))) | ~v1_funct_2(A_998, u1_struct_0(A_999), u1_struct_0(B_1000)) | ~v1_funct_1(A_998) | ~l1_pre_topc(B_1000) | ~v2_pre_topc(B_1000) | ~l1_pre_topc(A_999) | ~v2_pre_topc(A_999) | ~r1_tarski(A_998, k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_999), u1_pre_topc(A_999))), u1_struct_0(B_1000))))), inference(resolution, [status(thm)], [c_12, c_1309])).
% 24.36/13.63  tff(c_11225, plain, (![A_998, A_999]: (v5_pre_topc(A_998, A_999, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc(A_998, g1_pre_topc(u1_struct_0(A_999), u1_pre_topc(A_999)), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v1_funct_2(A_998, u1_struct_0(g1_pre_topc(u1_struct_0(A_999), u1_pre_topc(A_999))), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~m1_subset_1(A_998, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_999), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))))) | ~v1_funct_2(A_998, u1_struct_0(A_999), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~v1_funct_1(A_998) | ~l1_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_999) | ~v2_pre_topc(A_999) | ~r1_tarski(A_998, k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_999), u1_pre_topc(A_999))), '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_9627, c_11211])).
% 24.36/13.63  tff(c_11332, plain, (![A_1005, A_1006]: (v5_pre_topc(A_1005, A_1006, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc(A_1005, g1_pre_topc(u1_struct_0(A_1006), u1_pre_topc(A_1006)), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v1_funct_2(A_1005, u1_struct_0(g1_pre_topc(u1_struct_0(A_1006), u1_pre_topc(A_1006))), '#skF_4') | ~m1_subset_1(A_1005, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1006), '#skF_4'))) | ~v1_funct_2(A_1005, u1_struct_0(A_1006), '#skF_4') | ~v1_funct_1(A_1005) | ~l1_pre_topc(A_1006) | ~v2_pre_topc(A_1006) | ~r1_tarski(A_1005, k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1006), u1_pre_topc(A_1006))), '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1009, c_1010, c_9627, c_9627, c_9627, c_11225])).
% 24.36/13.63  tff(c_11335, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4') | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4'))), inference(resolution, [status(thm)], [c_9782, c_11332])).
% 24.36/13.63  tff(c_11347, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1031, c_72, c_70, c_58, c_1012, c_1033, c_9630, c_11335])).
% 24.36/13.63  tff(c_11585, plain, (![A_1033, A_1034, B_1035]: (v5_pre_topc(A_1033, A_1034, B_1035) | ~v5_pre_topc(A_1033, A_1034, g1_pre_topc(u1_struct_0(B_1035), u1_pre_topc(B_1035))) | ~v1_funct_2(A_1033, u1_struct_0(A_1034), u1_struct_0(g1_pre_topc(u1_struct_0(B_1035), u1_pre_topc(B_1035)))) | ~m1_subset_1(A_1033, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1034), u1_struct_0(B_1035)))) | ~v1_funct_2(A_1033, u1_struct_0(A_1034), u1_struct_0(B_1035)) | ~v1_funct_1(A_1033) | ~l1_pre_topc(B_1035) | ~v2_pre_topc(B_1035) | ~l1_pre_topc(A_1034) | ~v2_pre_topc(A_1034) | ~r1_tarski(A_1033, k2_zfmisc_1(u1_struct_0(A_1034), u1_struct_0(g1_pre_topc(u1_struct_0(B_1035), u1_pre_topc(B_1035))))))), inference(resolution, [status(thm)], [c_12, c_1183])).
% 24.36/13.63  tff(c_11609, plain, (![A_1033, A_1034]: (v5_pre_topc(A_1033, A_1034, '#skF_2') | ~v5_pre_topc(A_1033, A_1034, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2(A_1033, u1_struct_0(A_1034), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1(A_1033, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1034), u1_struct_0('#skF_2')))) | ~v1_funct_2(A_1033, u1_struct_0(A_1034), u1_struct_0('#skF_2')) | ~v1_funct_1(A_1033) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(A_1034) | ~v2_pre_topc(A_1034) | ~r1_tarski(A_1033, k2_zfmisc_1(u1_struct_0(A_1034), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))))))), inference(superposition, [status(thm), theory('equality')], [c_1014, c_11585])).
% 24.36/13.63  tff(c_15653, plain, (![A_1413, A_1414]: (v5_pre_topc(A_1413, A_1414, '#skF_2') | ~v5_pre_topc(A_1413, A_1414, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~m1_subset_1(A_1413, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1414), '#skF_4'))) | ~v1_funct_2(A_1413, u1_struct_0(A_1414), '#skF_4') | ~v1_funct_1(A_1413) | ~l1_pre_topc(A_1414) | ~v2_pre_topc(A_1414) | ~r1_tarski(A_1413, k2_zfmisc_1(u1_struct_0(A_1414), '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_9627, c_68, c_66, c_1014, c_1014, c_9627, c_1014, c_1014, c_11609])).
% 24.36/13.63  tff(c_15680, plain, (![A_1414]: (v5_pre_topc('#skF_4', A_1414, '#skF_2') | ~v5_pre_topc('#skF_4', A_1414, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1414), '#skF_4') | ~v1_funct_1('#skF_4') | ~l1_pre_topc(A_1414) | ~v2_pre_topc(A_1414) | ~r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0(A_1414), '#skF_4')))), inference(resolution, [status(thm)], [c_1033, c_15653])).
% 24.36/13.63  tff(c_15716, plain, (![A_1415]: (v5_pre_topc('#skF_4', A_1415, '#skF_2') | ~v5_pre_topc('#skF_4', A_1415, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1415), '#skF_4') | ~l1_pre_topc(A_1415) | ~v2_pre_topc(A_1415))), inference(demodulation, [status(thm), theory('equality')], [c_1031, c_58, c_15680])).
% 24.36/13.63  tff(c_15750, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_11347, c_15716])).
% 24.36/13.63  tff(c_15781, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_1012, c_15750])).
% 24.36/13.63  tff(c_15783, plain, $false, inference(negUnitSimplification, [status(thm)], [c_343, c_15781])).
% 24.36/13.63  tff(c_15784, plain, (u1_struct_0('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_527])).
% 24.36/13.63  tff(c_15796, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_15784, c_121])).
% 24.36/13.63  tff(c_15799, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_15784, c_81])).
% 24.36/13.63  tff(c_15798, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_15784, c_56])).
% 24.36/13.63  tff(c_152, plain, (r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))))), inference(resolution, [status(thm)], [c_54, c_10])).
% 24.36/13.63  tff(c_344, plain, (![A_111, B_112, A_113]: (k1_relset_1(A_111, B_112, A_113)=k1_relat_1(A_113) | ~r1_tarski(A_113, k2_zfmisc_1(A_111, B_112)))), inference(resolution, [status(thm)], [c_12, c_300])).
% 24.36/13.63  tff(c_359, plain, (k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_152, c_344])).
% 24.36/13.63  tff(c_16430, plain, (k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_15784, c_359])).
% 24.36/13.63  tff(c_15794, plain, (r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))))), inference(demodulation, [status(thm), theory('equality')], [c_15784, c_152])).
% 24.36/13.63  tff(c_16020, plain, (![B_1430, A_1431, C_1432]: (k1_xboole_0=B_1430 | k1_relset_1(A_1431, B_1430, C_1432)=A_1431 | ~v1_funct_2(C_1432, A_1431, B_1430) | ~m1_subset_1(C_1432, k1_zfmisc_1(k2_zfmisc_1(A_1431, B_1430))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 24.36/13.63  tff(c_16752, plain, (![B_1519, A_1520, A_1521]: (k1_xboole_0=B_1519 | k1_relset_1(A_1520, B_1519, A_1521)=A_1520 | ~v1_funct_2(A_1521, A_1520, B_1519) | ~r1_tarski(A_1521, k2_zfmisc_1(A_1520, B_1519)))), inference(resolution, [status(thm)], [c_12, c_16020])).
% 24.36/13.63  tff(c_16759, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0 | k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')=u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(resolution, [status(thm)], [c_15794, c_16752])).
% 24.36/13.63  tff(c_16782, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0 | u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_15798, c_16430, c_16759])).
% 24.36/13.63  tff(c_16803, plain, (u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_16782])).
% 24.36/13.63  tff(c_15797, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_15784, c_85])).
% 24.36/13.63  tff(c_15810, plain, (v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_15784, c_40])).
% 24.36/13.63  tff(c_15830, plain, (v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_15810])).
% 24.36/13.63  tff(c_15816, plain, (l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_15784, c_190])).
% 24.36/13.63  tff(c_15834, plain, (l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_15816])).
% 24.36/13.63  tff(c_15791, plain, (v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_15784, c_290])).
% 24.36/13.63  tff(c_15795, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))))), inference(demodulation, [status(thm), theory('equality')], [c_15784, c_54])).
% 24.36/13.63  tff(c_16308, plain, (![D_1463, A_1464, B_1465]: (v5_pre_topc(D_1463, A_1464, B_1465) | ~v5_pre_topc(D_1463, A_1464, g1_pre_topc(u1_struct_0(B_1465), u1_pre_topc(B_1465))) | ~m1_subset_1(D_1463, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1464), u1_struct_0(g1_pre_topc(u1_struct_0(B_1465), u1_pre_topc(B_1465)))))) | ~v1_funct_2(D_1463, u1_struct_0(A_1464), u1_struct_0(g1_pre_topc(u1_struct_0(B_1465), u1_pre_topc(B_1465)))) | ~m1_subset_1(D_1463, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1464), u1_struct_0(B_1465)))) | ~v1_funct_2(D_1463, u1_struct_0(A_1464), u1_struct_0(B_1465)) | ~v1_funct_1(D_1463) | ~l1_pre_topc(B_1465) | ~v2_pre_topc(B_1465) | ~l1_pre_topc(A_1464) | ~v2_pre_topc(A_1464))), inference(cnfTransformation, [status(thm)], [f_151])).
% 24.36/13.63  tff(c_16311, plain, (v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), '#skF_2') | ~v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_15795, c_16308])).
% 24.36/13.63  tff(c_16335, plain, (v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_15830, c_15834, c_68, c_66, c_58, c_15798, c_15791, c_16311])).
% 24.36/13.63  tff(c_17655, plain, (v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_15799, c_16803, c_15797, c_16803, c_16335])).
% 24.36/13.63  tff(c_16162, plain, (![D_1448, A_1449, B_1450]: (v5_pre_topc(D_1448, A_1449, B_1450) | ~v5_pre_topc(D_1448, g1_pre_topc(u1_struct_0(A_1449), u1_pre_topc(A_1449)), B_1450) | ~m1_subset_1(D_1448, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1449), u1_pre_topc(A_1449))), u1_struct_0(B_1450)))) | ~v1_funct_2(D_1448, u1_struct_0(g1_pre_topc(u1_struct_0(A_1449), u1_pre_topc(A_1449))), u1_struct_0(B_1450)) | ~m1_subset_1(D_1448, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1449), u1_struct_0(B_1450)))) | ~v1_funct_2(D_1448, u1_struct_0(A_1449), u1_struct_0(B_1450)) | ~v1_funct_1(D_1448) | ~l1_pre_topc(B_1450) | ~v2_pre_topc(B_1450) | ~l1_pre_topc(A_1449) | ~v2_pre_topc(A_1449))), inference(cnfTransformation, [status(thm)], [f_122])).
% 24.36/13.63  tff(c_18013, plain, (![A_1638, A_1639, B_1640]: (v5_pre_topc(A_1638, A_1639, B_1640) | ~v5_pre_topc(A_1638, g1_pre_topc(u1_struct_0(A_1639), u1_pre_topc(A_1639)), B_1640) | ~v1_funct_2(A_1638, u1_struct_0(g1_pre_topc(u1_struct_0(A_1639), u1_pre_topc(A_1639))), u1_struct_0(B_1640)) | ~m1_subset_1(A_1638, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1639), u1_struct_0(B_1640)))) | ~v1_funct_2(A_1638, u1_struct_0(A_1639), u1_struct_0(B_1640)) | ~v1_funct_1(A_1638) | ~l1_pre_topc(B_1640) | ~v2_pre_topc(B_1640) | ~l1_pre_topc(A_1639) | ~v2_pre_topc(A_1639) | ~r1_tarski(A_1638, k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1639), u1_pre_topc(A_1639))), u1_struct_0(B_1640))))), inference(resolution, [status(thm)], [c_12, c_16162])).
% 24.36/13.63  tff(c_18042, plain, (![A_1638, B_1640]: (v5_pre_topc(A_1638, '#skF_1', B_1640) | ~v5_pre_topc(A_1638, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_1640) | ~v1_funct_2(A_1638, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_1640)) | ~m1_subset_1(A_1638, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_1640)))) | ~v1_funct_2(A_1638, u1_struct_0('#skF_1'), u1_struct_0(B_1640)) | ~v1_funct_1(A_1638) | ~l1_pre_topc(B_1640) | ~v2_pre_topc(B_1640) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(A_1638, k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(B_1640))))), inference(superposition, [status(thm), theory('equality')], [c_15784, c_18013])).
% 24.36/13.63  tff(c_23307, plain, (![A_2117, B_2118]: (v5_pre_topc(A_2117, '#skF_1', B_2118) | ~v5_pre_topc(A_2117, g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), B_2118) | ~m1_subset_1(A_2117, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_2118)))) | ~v1_funct_2(A_2117, k1_relat_1('#skF_4'), u1_struct_0(B_2118)) | ~v1_funct_1(A_2117) | ~l1_pre_topc(B_2118) | ~v2_pre_topc(B_2118) | ~r1_tarski(A_2117, k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_2118))))), inference(demodulation, [status(thm), theory('equality')], [c_16803, c_72, c_70, c_15784, c_15784, c_16803, c_15784, c_15784, c_18042])).
% 24.36/13.63  tff(c_23336, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), '#skF_2') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~r1_tarski('#skF_4', k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_15797, c_23307])).
% 24.36/13.63  tff(c_23375, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_15796, c_68, c_66, c_58, c_15799, c_17655, c_23336])).
% 24.36/13.63  tff(c_23377, plain, $false, inference(negUnitSimplification, [status(thm)], [c_343, c_23375])).
% 24.36/13.63  tff(c_23378, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0), inference(splitRight, [status(thm)], [c_16782])).
% 24.36/13.63  tff(c_23383, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_23378, c_15798])).
% 24.36/13.63  tff(c_23381, plain, (r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_23378, c_15794])).
% 24.36/13.63  tff(c_23496, plain, (k1_xboole_0='#skF_4' | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), k1_xboole_0) | u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))=k1_xboole_0), inference(resolution, [status(thm)], [c_23381, c_515])).
% 24.36/13.63  tff(c_23511, plain, (k1_xboole_0='#skF_4' | u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_23383, c_23496])).
% 24.36/13.63  tff(c_23514, plain, (u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))=k1_xboole_0), inference(splitLeft, [status(thm)], [c_23511])).
% 24.36/13.63  tff(c_23379, plain, (u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))!=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_16782])).
% 24.36/13.63  tff(c_23552, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_23514, c_23379])).
% 24.36/13.63  tff(c_16, plain, (![A_9, B_10, C_11]: (m1_subset_1(k1_relset_1(A_9, B_10, C_11), k1_zfmisc_1(A_9)) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 24.36/13.63  tff(c_469, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))))), inference(superposition, [status(thm), theory('equality')], [c_315, c_16])).
% 24.36/13.63  tff(c_479, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_469])).
% 24.36/13.63  tff(c_16007, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_15784, c_479])).
% 24.36/13.63  tff(c_16014, plain, (r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))))), inference(resolution, [status(thm)], [c_16007, c_10])).
% 24.36/13.63  tff(c_23554, plain, (r1_tarski(k1_relat_1('#skF_4'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_23514, c_16014])).
% 24.36/13.63  tff(c_23642, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_23554, c_113])).
% 24.36/13.63  tff(c_23648, plain, $false, inference(negUnitSimplification, [status(thm)], [c_23552, c_23642])).
% 24.36/13.63  tff(c_23649, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_23511])).
% 24.36/13.63  tff(c_191, plain, (![A_84]: (r1_tarski(u1_pre_topc(A_84), k1_zfmisc_1(u1_struct_0(A_84))) | ~l1_pre_topc(A_84))), inference(resolution, [status(thm)], [c_179, c_10])).
% 24.36/13.63  tff(c_23435, plain, (r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), k1_zfmisc_1(k1_xboole_0)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_23378, c_191])).
% 24.36/13.63  tff(c_24712, plain, (r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), k1_zfmisc_1('#skF_4')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_23649, c_23435])).
% 24.36/13.63  tff(c_24713, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_24712])).
% 24.36/13.63  tff(c_24719, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_190, c_24713])).
% 24.36/13.63  tff(c_24725, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_24719])).
% 24.36/13.63  tff(c_24727, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_24712])).
% 24.36/13.63  tff(c_23432, plain, (v2_pre_topc(g1_pre_topc(k1_xboole_0, u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_23378, c_40])).
% 24.36/13.63  tff(c_25521, plain, (v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_24727, c_23649, c_23432])).
% 24.36/13.63  tff(c_25522, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_25521])).
% 24.36/13.63  tff(c_25528, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_40, c_25522])).
% 24.36/13.63  tff(c_25534, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_25528])).
% 24.36/13.63  tff(c_25536, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_25521])).
% 24.36/13.63  tff(c_23676, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_23649, c_23649, c_455])).
% 24.36/13.63  tff(c_23652, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_23649, c_23383])).
% 24.36/13.63  tff(c_24318, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_23676, c_23652])).
% 24.36/13.63  tff(c_23697, plain, (v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_23676, c_15791])).
% 24.36/13.63  tff(c_23653, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_23649, c_23378])).
% 24.36/13.63  tff(c_15891, plain, (![C_1418, B_1419]: (v1_funct_2(C_1418, k1_xboole_0, B_1419) | k1_relset_1(k1_xboole_0, B_1419, C_1418)!=k1_xboole_0 | ~m1_subset_1(C_1418, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_1419))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 24.36/13.63  tff(c_15903, plain, (![B_1419]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_1419) | k1_relset_1(k1_xboole_0, B_1419, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_15891])).
% 24.36/13.63  tff(c_15908, plain, (![B_1419]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_1419))), inference(demodulation, [status(thm), theory('equality')], [c_459, c_15903])).
% 24.36/13.63  tff(c_23671, plain, (![B_1419]: (v1_funct_2('#skF_4', '#skF_4', B_1419))), inference(demodulation, [status(thm), theory('equality')], [c_23649, c_23649, c_15908])).
% 24.36/13.63  tff(c_23716, plain, (u1_struct_0('#skF_1')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_23676, c_15784])).
% 24.36/13.63  tff(c_16183, plain, (![A_1449, B_1450]: (v5_pre_topc(k1_xboole_0, A_1449, B_1450) | ~v5_pre_topc(k1_xboole_0, g1_pre_topc(u1_struct_0(A_1449), u1_pre_topc(A_1449)), B_1450) | ~v1_funct_2(k1_xboole_0, u1_struct_0(g1_pre_topc(u1_struct_0(A_1449), u1_pre_topc(A_1449))), u1_struct_0(B_1450)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1449), u1_struct_0(B_1450)))) | ~v1_funct_2(k1_xboole_0, u1_struct_0(A_1449), u1_struct_0(B_1450)) | ~v1_funct_1(k1_xboole_0) | ~l1_pre_topc(B_1450) | ~v2_pre_topc(B_1450) | ~l1_pre_topc(A_1449) | ~v2_pre_topc(A_1449))), inference(resolution, [status(thm)], [c_8, c_16162])).
% 24.36/13.63  tff(c_16192, plain, (![A_1449, B_1450]: (v5_pre_topc(k1_xboole_0, A_1449, B_1450) | ~v5_pre_topc(k1_xboole_0, g1_pre_topc(u1_struct_0(A_1449), u1_pre_topc(A_1449)), B_1450) | ~v1_funct_2(k1_xboole_0, u1_struct_0(g1_pre_topc(u1_struct_0(A_1449), u1_pre_topc(A_1449))), u1_struct_0(B_1450)) | ~v1_funct_2(k1_xboole_0, u1_struct_0(A_1449), u1_struct_0(B_1450)) | ~v1_funct_1(k1_xboole_0) | ~l1_pre_topc(B_1450) | ~v2_pre_topc(B_1450) | ~l1_pre_topc(A_1449) | ~v2_pre_topc(A_1449))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_16183])).
% 24.36/13.63  tff(c_24141, plain, (![A_2155, B_2156]: (v5_pre_topc('#skF_4', A_2155, B_2156) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_2155), u1_pre_topc(A_2155)), B_2156) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_2155), u1_pre_topc(A_2155))), u1_struct_0(B_2156)) | ~v1_funct_2('#skF_4', u1_struct_0(A_2155), u1_struct_0(B_2156)) | ~l1_pre_topc(B_2156) | ~v2_pre_topc(B_2156) | ~l1_pre_topc(A_2155) | ~v2_pre_topc(A_2155))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_23649, c_23649, c_23649, c_23649, c_23649, c_16192])).
% 24.36/13.63  tff(c_24144, plain, (![B_2156]: (v5_pre_topc('#skF_4', '#skF_1', B_2156) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_2156) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), u1_struct_0(B_2156)) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0(B_2156)) | ~l1_pre_topc(B_2156) | ~v2_pre_topc(B_2156) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_23716, c_24141])).
% 24.36/13.63  tff(c_27209, plain, (![B_2403]: (v5_pre_topc('#skF_4', '#skF_1', B_2403) | ~v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), B_2403) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), u1_struct_0(B_2403)) | ~l1_pre_topc(B_2403) | ~v2_pre_topc(B_2403))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_23671, c_23716, c_23716, c_24144])).
% 24.36/13.63  tff(c_27215, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), '#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_23653, c_27209])).
% 24.36/13.63  tff(c_27221, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_25536, c_24727, c_24318, c_23697, c_27215])).
% 24.36/13.63  tff(c_16332, plain, (![A_1464, B_1465]: (v5_pre_topc(k1_xboole_0, A_1464, B_1465) | ~v5_pre_topc(k1_xboole_0, A_1464, g1_pre_topc(u1_struct_0(B_1465), u1_pre_topc(B_1465))) | ~v1_funct_2(k1_xboole_0, u1_struct_0(A_1464), u1_struct_0(g1_pre_topc(u1_struct_0(B_1465), u1_pre_topc(B_1465)))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1464), u1_struct_0(B_1465)))) | ~v1_funct_2(k1_xboole_0, u1_struct_0(A_1464), u1_struct_0(B_1465)) | ~v1_funct_1(k1_xboole_0) | ~l1_pre_topc(B_1465) | ~v2_pre_topc(B_1465) | ~l1_pre_topc(A_1464) | ~v2_pre_topc(A_1464))), inference(resolution, [status(thm)], [c_8, c_16308])).
% 24.36/13.63  tff(c_16344, plain, (![A_1464, B_1465]: (v5_pre_topc(k1_xboole_0, A_1464, B_1465) | ~v5_pre_topc(k1_xboole_0, A_1464, g1_pre_topc(u1_struct_0(B_1465), u1_pre_topc(B_1465))) | ~v1_funct_2(k1_xboole_0, u1_struct_0(A_1464), u1_struct_0(g1_pre_topc(u1_struct_0(B_1465), u1_pre_topc(B_1465)))) | ~v1_funct_2(k1_xboole_0, u1_struct_0(A_1464), u1_struct_0(B_1465)) | ~v1_funct_1(k1_xboole_0) | ~l1_pre_topc(B_1465) | ~v2_pre_topc(B_1465) | ~l1_pre_topc(A_1464) | ~v2_pre_topc(A_1464))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_16332])).
% 24.36/13.63  tff(c_24394, plain, (![A_2170, B_2171]: (v5_pre_topc('#skF_4', A_2170, B_2171) | ~v5_pre_topc('#skF_4', A_2170, g1_pre_topc(u1_struct_0(B_2171), u1_pre_topc(B_2171))) | ~v1_funct_2('#skF_4', u1_struct_0(A_2170), u1_struct_0(g1_pre_topc(u1_struct_0(B_2171), u1_pre_topc(B_2171)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_2170), u1_struct_0(B_2171)) | ~l1_pre_topc(B_2171) | ~v2_pre_topc(B_2171) | ~l1_pre_topc(A_2170) | ~v2_pre_topc(A_2170))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_23649, c_23649, c_23649, c_23649, c_23649, c_16344])).
% 24.36/13.63  tff(c_24409, plain, (![B_2171]: (v5_pre_topc('#skF_4', '#skF_1', B_2171) | ~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0(B_2171), u1_pre_topc(B_2171))) | ~v1_funct_2('#skF_4', '#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(B_2171), u1_pre_topc(B_2171)))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0(B_2171)) | ~l1_pre_topc(B_2171) | ~v2_pre_topc(B_2171) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_23716, c_24394])).
% 24.36/13.63  tff(c_24423, plain, (![B_2171]: (v5_pre_topc('#skF_4', '#skF_1', B_2171) | ~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0(B_2171), u1_pre_topc(B_2171))) | ~l1_pre_topc(B_2171) | ~v2_pre_topc(B_2171))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_23671, c_23716, c_23671, c_24409])).
% 24.36/13.63  tff(c_27262, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_27221, c_24423])).
% 24.36/13.63  tff(c_27268, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_27262])).
% 24.36/13.63  tff(c_27270, plain, $false, inference(negUnitSimplification, [status(thm)], [c_343, c_27268])).
% 24.36/13.63  tff(c_27271, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_82])).
% 24.36/13.63  tff(c_27282, plain, (![A_2410, B_2411, C_2412]: (k1_relset_1(A_2410, B_2411, C_2412)=k1_relat_1(C_2412) | ~m1_subset_1(C_2412, k1_zfmisc_1(k2_zfmisc_1(A_2410, B_2411))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 24.36/13.63  tff(c_27298, plain, (k1_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_85, c_27282])).
% 24.36/13.63  tff(c_27822, plain, (![B_2468, A_2469, C_2470]: (k1_xboole_0=B_2468 | k1_relset_1(A_2469, B_2468, C_2470)=A_2469 | ~v1_funct_2(C_2470, A_2469, B_2468) | ~m1_subset_1(C_2470, k1_zfmisc_1(k2_zfmisc_1(A_2469, B_2468))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 24.36/13.63  tff(c_27832, plain, (u1_struct_0('#skF_2')=k1_xboole_0 | k1_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4')=u1_struct_0('#skF_1') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_85, c_27822])).
% 24.36/13.63  tff(c_27847, plain, (u1_struct_0('#skF_2')=k1_xboole_0 | u1_struct_0('#skF_1')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_27298, c_27832])).
% 24.36/13.63  tff(c_27851, plain, (u1_struct_0('#skF_1')=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_27847])).
% 24.36/13.63  tff(c_27356, plain, (![A_2420, B_2421, C_2422]: (m1_subset_1(k1_relset_1(A_2420, B_2421, C_2422), k1_zfmisc_1(A_2420)) | ~m1_subset_1(C_2422, k1_zfmisc_1(k2_zfmisc_1(A_2420, B_2421))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 24.36/13.63  tff(c_27379, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_27298, c_27356])).
% 24.36/13.63  tff(c_27389, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_27379])).
% 24.36/13.63  tff(c_27517, plain, (r1_tarski(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_27389, c_10])).
% 24.36/13.63  tff(c_27520, plain, (u1_struct_0('#skF_1')=k1_relat_1('#skF_4') | ~r1_tarski(u1_struct_0('#skF_1'), k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_27517, c_2])).
% 24.36/13.63  tff(c_27545, plain, (~r1_tarski(u1_struct_0('#skF_1'), k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_27520])).
% 24.36/13.63  tff(c_27855, plain, (~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_27851, c_27545])).
% 24.36/13.63  tff(c_27872, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_27855])).
% 24.36/13.63  tff(c_27873, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_27847])).
% 24.36/13.63  tff(c_27885, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_27873, c_81])).
% 24.36/13.63  tff(c_27882, plain, (r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0('#skF_1'), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_27873, c_121])).
% 24.36/13.63  tff(c_27469, plain, (![C_2425, A_2426]: (k1_xboole_0=C_2425 | ~v1_funct_2(C_2425, A_2426, k1_xboole_0) | k1_xboole_0=A_2426 | ~m1_subset_1(C_2425, k1_zfmisc_1(k2_zfmisc_1(A_2426, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 24.36/13.63  tff(c_27483, plain, (![A_4, A_2426]: (k1_xboole_0=A_4 | ~v1_funct_2(A_4, A_2426, k1_xboole_0) | k1_xboole_0=A_2426 | ~r1_tarski(A_4, k2_zfmisc_1(A_2426, k1_xboole_0)))), inference(resolution, [status(thm)], [c_12, c_27469])).
% 24.36/13.63  tff(c_27976, plain, (k1_xboole_0='#skF_4' | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), k1_xboole_0) | u1_struct_0('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_27882, c_27483])).
% 24.36/13.63  tff(c_27984, plain, (k1_xboole_0='#skF_4' | u1_struct_0('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_27885, c_27976])).
% 24.36/13.63  tff(c_27987, plain, (u1_struct_0('#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_27984])).
% 24.36/13.63  tff(c_28032, plain, (~r1_tarski(k1_xboole_0, k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_27987, c_27545])).
% 24.36/13.63  tff(c_28038, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_101, c_28032])).
% 24.36/13.63  tff(c_28039, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_27984])).
% 24.36/13.63  tff(c_28046, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28039, c_27885])).
% 24.36/13.63  tff(c_28068, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_28039, c_101])).
% 24.36/13.63  tff(c_28070, plain, (![A_3]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_28039, c_8])).
% 24.36/13.63  tff(c_27300, plain, (![A_2410, B_2411]: (k1_relset_1(A_2410, B_2411, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_27282])).
% 24.36/13.63  tff(c_27382, plain, (![A_2410, B_2411]: (m1_subset_1(k1_relat_1(k1_xboole_0), k1_zfmisc_1(A_2410)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_2410, B_2411))))), inference(superposition, [status(thm), theory('equality')], [c_27300, c_27356])).
% 24.36/13.63  tff(c_27411, plain, (![A_2423]: (m1_subset_1(k1_relat_1(k1_xboole_0), k1_zfmisc_1(A_2423)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_27382])).
% 24.36/13.63  tff(c_27434, plain, (![A_2424]: (r1_tarski(k1_relat_1(k1_xboole_0), A_2424))), inference(resolution, [status(thm)], [c_27411, c_10])).
% 24.36/13.63  tff(c_27456, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_27434, c_113])).
% 24.36/13.63  tff(c_27460, plain, (![A_2410, B_2411]: (k1_relset_1(A_2410, B_2411, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_27456, c_27300])).
% 24.36/13.63  tff(c_27524, plain, (![C_2430, B_2431]: (v1_funct_2(C_2430, k1_xboole_0, B_2431) | k1_relset_1(k1_xboole_0, B_2431, C_2430)!=k1_xboole_0 | ~m1_subset_1(C_2430, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_2431))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 24.36/13.63  tff(c_27536, plain, (![B_2431]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_2431) | k1_relset_1(k1_xboole_0, B_2431, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_27524])).
% 24.36/13.63  tff(c_27541, plain, (![B_2431]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_2431))), inference(demodulation, [status(thm), theory('equality')], [c_27460, c_27536])).
% 24.36/13.63  tff(c_28059, plain, (![B_2431]: (v1_funct_2('#skF_4', '#skF_4', B_2431))), inference(demodulation, [status(thm), theory('equality')], [c_28039, c_28039, c_27541])).
% 24.36/13.63  tff(c_28048, plain, (u1_struct_0('#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_28039, c_27873])).
% 24.36/13.63  tff(c_28063, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_28039, c_28039, c_27456])).
% 24.36/13.63  tff(c_27297, plain, (k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_27282])).
% 24.36/13.63  tff(c_27829, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0 | k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')=u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(resolution, [status(thm)], [c_54, c_27822])).
% 24.36/13.63  tff(c_27844, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0 | u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_27297, c_27829])).
% 24.36/13.63  tff(c_28412, plain, (u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))='#skF_4' | u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_28063, c_28048, c_28039, c_27844])).
% 24.36/13.63  tff(c_28413, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))='#skF_4'), inference(splitLeft, [status(thm)], [c_28412])).
% 24.36/13.63  tff(c_28149, plain, (![D_2475, A_2476, B_2477]: (v5_pre_topc(D_2475, g1_pre_topc(u1_struct_0(A_2476), u1_pre_topc(A_2476)), B_2477) | ~v5_pre_topc(D_2475, A_2476, B_2477) | ~m1_subset_1(D_2475, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2476), u1_pre_topc(A_2476))), u1_struct_0(B_2477)))) | ~v1_funct_2(D_2475, u1_struct_0(g1_pre_topc(u1_struct_0(A_2476), u1_pre_topc(A_2476))), u1_struct_0(B_2477)) | ~m1_subset_1(D_2475, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2476), u1_struct_0(B_2477)))) | ~v1_funct_2(D_2475, u1_struct_0(A_2476), u1_struct_0(B_2477)) | ~v1_funct_1(D_2475) | ~l1_pre_topc(B_2477) | ~v2_pre_topc(B_2477) | ~l1_pre_topc(A_2476) | ~v2_pre_topc(A_2476))), inference(cnfTransformation, [status(thm)], [f_122])).
% 24.36/13.63  tff(c_30463, plain, (![A_2718, A_2719, B_2720]: (v5_pre_topc(A_2718, g1_pre_topc(u1_struct_0(A_2719), u1_pre_topc(A_2719)), B_2720) | ~v5_pre_topc(A_2718, A_2719, B_2720) | ~v1_funct_2(A_2718, u1_struct_0(g1_pre_topc(u1_struct_0(A_2719), u1_pre_topc(A_2719))), u1_struct_0(B_2720)) | ~m1_subset_1(A_2718, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2719), u1_struct_0(B_2720)))) | ~v1_funct_2(A_2718, u1_struct_0(A_2719), u1_struct_0(B_2720)) | ~v1_funct_1(A_2718) | ~l1_pre_topc(B_2720) | ~v2_pre_topc(B_2720) | ~l1_pre_topc(A_2719) | ~v2_pre_topc(A_2719) | ~r1_tarski(A_2718, k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2719), u1_pre_topc(A_2719))), u1_struct_0(B_2720))))), inference(resolution, [status(thm)], [c_12, c_28149])).
% 24.36/13.63  tff(c_30485, plain, (![A_2718, B_2720]: (v5_pre_topc(A_2718, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_2720) | ~v5_pre_topc(A_2718, '#skF_1', B_2720) | ~v1_funct_2(A_2718, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_2720)) | ~m1_subset_1(A_2718, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_2720)))) | ~v1_funct_2(A_2718, u1_struct_0('#skF_1'), u1_struct_0(B_2720)) | ~v1_funct_1(A_2718) | ~l1_pre_topc(B_2720) | ~v2_pre_topc(B_2720) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(A_2718, k2_zfmisc_1('#skF_4', u1_struct_0(B_2720))))), inference(superposition, [status(thm), theory('equality')], [c_28413, c_30463])).
% 24.36/13.63  tff(c_30967, plain, (![A_2756, B_2757]: (v5_pre_topc(A_2756, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_2757) | ~v5_pre_topc(A_2756, '#skF_1', B_2757) | ~v1_funct_2(A_2756, '#skF_4', u1_struct_0(B_2757)) | ~m1_subset_1(A_2756, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_2757)))) | ~v1_funct_2(A_2756, u1_struct_0('#skF_1'), u1_struct_0(B_2757)) | ~v1_funct_1(A_2756) | ~l1_pre_topc(B_2757) | ~v2_pre_topc(B_2757) | ~r1_tarski(A_2756, k2_zfmisc_1('#skF_4', u1_struct_0(B_2757))))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_28413, c_30485])).
% 24.36/13.63  tff(c_30989, plain, (![A_2756]: (v5_pre_topc(A_2756, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~v5_pre_topc(A_2756, '#skF_1', '#skF_2') | ~v1_funct_2(A_2756, '#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1(A_2756, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), '#skF_4'))) | ~v1_funct_2(A_2756, u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(A_2756) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~r1_tarski(A_2756, k2_zfmisc_1('#skF_4', u1_struct_0('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_28048, c_30967])).
% 24.36/13.64  tff(c_31007, plain, (![A_2756]: (v5_pre_topc(A_2756, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~v5_pre_topc(A_2756, '#skF_1', '#skF_2') | ~v1_funct_2(A_2756, '#skF_4', '#skF_4') | ~m1_subset_1(A_2756, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), '#skF_4'))) | ~v1_funct_2(A_2756, u1_struct_0('#skF_1'), '#skF_4') | ~v1_funct_1(A_2756) | ~r1_tarski(A_2756, k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_28048, c_68, c_66, c_28048, c_28048, c_30989])).
% 24.36/13.64  tff(c_27334, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_27271, c_84])).
% 24.36/13.64  tff(c_27877, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_27873, c_27334])).
% 24.36/13.64  tff(c_28526, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_28039, c_27877])).
% 24.36/13.64  tff(c_28489, plain, (r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), k1_zfmisc_1('#skF_4')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_28413, c_191])).
% 24.36/13.64  tff(c_28799, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_28489])).
% 24.36/13.64  tff(c_28805, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_190, c_28799])).
% 24.36/13.64  tff(c_28811, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_28805])).
% 24.36/13.64  tff(c_28813, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_28489])).
% 24.36/13.64  tff(c_28486, plain, (v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_28413, c_40])).
% 24.36/13.64  tff(c_29516, plain, (v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28813, c_28486])).
% 24.36/13.64  tff(c_29517, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_29516])).
% 24.36/13.64  tff(c_29523, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_29517])).
% 24.36/13.64  tff(c_29529, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_29523])).
% 24.36/13.64  tff(c_29531, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_29516])).
% 24.36/13.64  tff(c_28237, plain, (![D_2481, A_2482, B_2483]: (v5_pre_topc(D_2481, A_2482, g1_pre_topc(u1_struct_0(B_2483), u1_pre_topc(B_2483))) | ~v5_pre_topc(D_2481, A_2482, B_2483) | ~m1_subset_1(D_2481, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2482), u1_struct_0(g1_pre_topc(u1_struct_0(B_2483), u1_pre_topc(B_2483)))))) | ~v1_funct_2(D_2481, u1_struct_0(A_2482), u1_struct_0(g1_pre_topc(u1_struct_0(B_2483), u1_pre_topc(B_2483)))) | ~m1_subset_1(D_2481, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2482), u1_struct_0(B_2483)))) | ~v1_funct_2(D_2481, u1_struct_0(A_2482), u1_struct_0(B_2483)) | ~v1_funct_1(D_2481) | ~l1_pre_topc(B_2483) | ~v2_pre_topc(B_2483) | ~l1_pre_topc(A_2482) | ~v2_pre_topc(A_2482))), inference(cnfTransformation, [status(thm)], [f_151])).
% 24.36/13.64  tff(c_28241, plain, (![A_2482, B_2483]: (v5_pre_topc('#skF_4', A_2482, g1_pre_topc(u1_struct_0(B_2483), u1_pre_topc(B_2483))) | ~v5_pre_topc('#skF_4', A_2482, B_2483) | ~v1_funct_2('#skF_4', u1_struct_0(A_2482), u1_struct_0(g1_pre_topc(u1_struct_0(B_2483), u1_pre_topc(B_2483)))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2482), u1_struct_0(B_2483)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_2482), u1_struct_0(B_2483)) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(B_2483) | ~v2_pre_topc(B_2483) | ~l1_pre_topc(A_2482) | ~v2_pre_topc(A_2482))), inference(resolution, [status(thm)], [c_28070, c_28237])).
% 24.36/13.64  tff(c_35583, plain, (![A_3092, B_3093]: (v5_pre_topc('#skF_4', A_3092, g1_pre_topc(u1_struct_0(B_3093), u1_pre_topc(B_3093))) | ~v5_pre_topc('#skF_4', A_3092, B_3093) | ~v1_funct_2('#skF_4', u1_struct_0(A_3092), u1_struct_0(g1_pre_topc(u1_struct_0(B_3093), u1_pre_topc(B_3093)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_3092), u1_struct_0(B_3093)) | ~l1_pre_topc(B_3093) | ~v2_pre_topc(B_3093) | ~l1_pre_topc(A_3092) | ~v2_pre_topc(A_3092))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_28070, c_28241])).
% 24.36/13.64  tff(c_35589, plain, (![B_3093]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0(B_3093), u1_pre_topc(B_3093))) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_3093) | ~v1_funct_2('#skF_4', '#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(B_3093), u1_pre_topc(B_3093)))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_3093)) | ~l1_pre_topc(B_3093) | ~v2_pre_topc(B_3093) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_28413, c_35583])).
% 24.36/13.64  tff(c_35711, plain, (![B_3097]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0(B_3097), u1_pre_topc(B_3097))) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_3097) | ~l1_pre_topc(B_3097) | ~v2_pre_topc(B_3097))), inference(demodulation, [status(thm), theory('equality')], [c_29531, c_28813, c_28059, c_28413, c_28059, c_35589])).
% 24.36/13.64  tff(c_35758, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_28048, c_35711])).
% 24.36/13.64  tff(c_35809, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_35758])).
% 24.36/13.64  tff(c_35810, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_28526, c_35809])).
% 24.36/13.64  tff(c_35815, plain, (~v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_4', '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4') | ~v1_funct_1('#skF_4') | ~r1_tarski('#skF_4', k2_zfmisc_1('#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_31007, c_35810])).
% 24.36/13.64  tff(c_35831, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28068, c_58, c_28046, c_28070, c_28059, c_27271, c_35815])).
% 24.36/13.64  tff(c_35832, plain, (u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))='#skF_4'), inference(splitRight, [status(thm)], [c_28412])).
% 24.36/13.64  tff(c_37927, plain, (![A_3321, A_3322, B_3323]: (v5_pre_topc(A_3321, A_3322, g1_pre_topc(u1_struct_0(B_3323), u1_pre_topc(B_3323))) | ~v5_pre_topc(A_3321, A_3322, B_3323) | ~v1_funct_2(A_3321, u1_struct_0(A_3322), u1_struct_0(g1_pre_topc(u1_struct_0(B_3323), u1_pre_topc(B_3323)))) | ~m1_subset_1(A_3321, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3322), u1_struct_0(B_3323)))) | ~v1_funct_2(A_3321, u1_struct_0(A_3322), u1_struct_0(B_3323)) | ~v1_funct_1(A_3321) | ~l1_pre_topc(B_3323) | ~v2_pre_topc(B_3323) | ~l1_pre_topc(A_3322) | ~v2_pre_topc(A_3322) | ~r1_tarski(A_3321, k2_zfmisc_1(u1_struct_0(A_3322), u1_struct_0(g1_pre_topc(u1_struct_0(B_3323), u1_pre_topc(B_3323))))))), inference(resolution, [status(thm)], [c_12, c_28237])).
% 24.36/13.64  tff(c_37955, plain, (![A_3321, A_3322]: (v5_pre_topc(A_3321, A_3322, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc(A_3321, A_3322, '#skF_2') | ~v1_funct_2(A_3321, u1_struct_0(A_3322), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1(A_3321, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3322), u1_struct_0('#skF_2')))) | ~v1_funct_2(A_3321, u1_struct_0(A_3322), u1_struct_0('#skF_2')) | ~v1_funct_1(A_3321) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(A_3322) | ~v2_pre_topc(A_3322) | ~r1_tarski(A_3321, k2_zfmisc_1(u1_struct_0(A_3322), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))))))), inference(superposition, [status(thm), theory('equality')], [c_28048, c_37927])).
% 24.36/13.64  tff(c_42018, plain, (![A_3692, A_3693]: (v5_pre_topc(A_3692, A_3693, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc(A_3692, A_3693, '#skF_2') | ~m1_subset_1(A_3692, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3693), '#skF_4'))) | ~v1_funct_2(A_3692, u1_struct_0(A_3693), '#skF_4') | ~v1_funct_1(A_3692) | ~l1_pre_topc(A_3693) | ~v2_pre_topc(A_3693) | ~r1_tarski(A_3692, k2_zfmisc_1(u1_struct_0(A_3693), '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_35832, c_68, c_66, c_28048, c_28048, c_35832, c_28048, c_28048, c_37955])).
% 24.36/13.64  tff(c_42045, plain, (![A_3693]: (v5_pre_topc('#skF_4', A_3693, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', A_3693, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0(A_3693), '#skF_4') | ~v1_funct_1('#skF_4') | ~l1_pre_topc(A_3693) | ~v2_pre_topc(A_3693) | ~r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0(A_3693), '#skF_4')))), inference(resolution, [status(thm)], [c_28070, c_42018])).
% 24.36/13.64  tff(c_42081, plain, (![A_3694]: (v5_pre_topc('#skF_4', A_3694, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', A_3694, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0(A_3694), '#skF_4') | ~l1_pre_topc(A_3694) | ~v2_pre_topc(A_3694))), inference(demodulation, [status(thm), theory('equality')], [c_28068, c_58, c_42045])).
% 24.36/13.64  tff(c_27884, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_27873, c_56])).
% 24.36/13.64  tff(c_28047, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_28039, c_27884])).
% 24.36/13.64  tff(c_35835, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_35832, c_28047])).
% 24.36/13.64  tff(c_27895, plain, (v2_pre_topc(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_27873, c_40])).
% 24.36/13.64  tff(c_27915, plain, (v2_pre_topc(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_27895])).
% 24.36/13.64  tff(c_28042, plain, (v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_28039, c_27915])).
% 24.36/13.64  tff(c_27901, plain, (l1_pre_topc(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_27873, c_190])).
% 24.36/13.64  tff(c_27919, plain, (l1_pre_topc(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_27901])).
% 24.36/13.64  tff(c_28044, plain, (l1_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_28039, c_27919])).
% 24.36/13.64  tff(c_38043, plain, (![A_3337, A_3338, B_3339]: (v5_pre_topc(A_3337, g1_pre_topc(u1_struct_0(A_3338), u1_pre_topc(A_3338)), B_3339) | ~v5_pre_topc(A_3337, A_3338, B_3339) | ~v1_funct_2(A_3337, u1_struct_0(g1_pre_topc(u1_struct_0(A_3338), u1_pre_topc(A_3338))), u1_struct_0(B_3339)) | ~m1_subset_1(A_3337, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3338), u1_struct_0(B_3339)))) | ~v1_funct_2(A_3337, u1_struct_0(A_3338), u1_struct_0(B_3339)) | ~v1_funct_1(A_3337) | ~l1_pre_topc(B_3339) | ~v2_pre_topc(B_3339) | ~l1_pre_topc(A_3338) | ~v2_pre_topc(A_3338) | ~r1_tarski(A_3337, k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_3338), u1_pre_topc(A_3338))), u1_struct_0(B_3339))))), inference(resolution, [status(thm)], [c_12, c_28149])).
% 24.36/13.64  tff(c_38065, plain, (![A_3337, A_3338]: (v5_pre_topc(A_3337, g1_pre_topc(u1_struct_0(A_3338), u1_pre_topc(A_3338)), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc(A_3337, A_3338, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v1_funct_2(A_3337, u1_struct_0(g1_pre_topc(u1_struct_0(A_3338), u1_pre_topc(A_3338))), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~m1_subset_1(A_3337, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3338), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))))) | ~v1_funct_2(A_3337, u1_struct_0(A_3338), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~v1_funct_1(A_3337) | ~l1_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_3338) | ~v2_pre_topc(A_3338) | ~r1_tarski(A_3337, k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_3338), u1_pre_topc(A_3338))), '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_35832, c_38043])).
% 24.36/13.64  tff(c_38157, plain, (![A_3345, A_3346]: (v5_pre_topc(A_3345, g1_pre_topc(u1_struct_0(A_3346), u1_pre_topc(A_3346)), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc(A_3345, A_3346, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v1_funct_2(A_3345, u1_struct_0(g1_pre_topc(u1_struct_0(A_3346), u1_pre_topc(A_3346))), '#skF_4') | ~m1_subset_1(A_3345, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3346), '#skF_4'))) | ~v1_funct_2(A_3345, u1_struct_0(A_3346), '#skF_4') | ~v1_funct_1(A_3345) | ~l1_pre_topc(A_3346) | ~v2_pre_topc(A_3346) | ~r1_tarski(A_3345, k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_3346), u1_pre_topc(A_3346))), '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_28042, c_28044, c_35832, c_35832, c_35832, c_38065])).
% 24.36/13.64  tff(c_35947, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_28039, c_27877])).
% 24.36/13.64  tff(c_38167, plain, (~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4') | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4'))), inference(resolution, [status(thm)], [c_38157, c_35947])).
% 24.36/13.64  tff(c_38183, plain, (~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_28068, c_72, c_70, c_58, c_28046, c_28070, c_35835, c_38167])).
% 24.36/13.64  tff(c_42102, plain, (~v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42081, c_38183])).
% 24.36/13.64  tff(c_42143, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_28046, c_27271, c_42102])).
% 24.36/13.64  tff(c_42144, plain, (u1_struct_0('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_27520])).
% 24.36/13.64  tff(c_42159, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42144, c_81])).
% 24.36/13.64  tff(c_42158, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_42144, c_56])).
% 24.36/13.64  tff(c_27312, plain, (![A_2415, B_2416, A_2417]: (k1_relset_1(A_2415, B_2416, A_2417)=k1_relat_1(A_2417) | ~r1_tarski(A_2417, k2_zfmisc_1(A_2415, B_2416)))), inference(resolution, [status(thm)], [c_12, c_27282])).
% 24.36/13.64  tff(c_27327, plain, (k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_152, c_27312])).
% 24.36/13.64  tff(c_42720, plain, (k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42144, c_27327])).
% 24.36/13.64  tff(c_42154, plain, (r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))))), inference(demodulation, [status(thm), theory('equality')], [c_42144, c_152])).
% 24.36/13.64  tff(c_42338, plain, (![B_3703, A_3704, C_3705]: (k1_xboole_0=B_3703 | k1_relset_1(A_3704, B_3703, C_3705)=A_3704 | ~v1_funct_2(C_3705, A_3704, B_3703) | ~m1_subset_1(C_3705, k1_zfmisc_1(k2_zfmisc_1(A_3704, B_3703))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 24.36/13.64  tff(c_43101, plain, (![B_3796, A_3797, A_3798]: (k1_xboole_0=B_3796 | k1_relset_1(A_3797, B_3796, A_3798)=A_3797 | ~v1_funct_2(A_3798, A_3797, B_3796) | ~r1_tarski(A_3798, k2_zfmisc_1(A_3797, B_3796)))), inference(resolution, [status(thm)], [c_12, c_42338])).
% 24.36/13.64  tff(c_43116, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0 | k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')=u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(resolution, [status(thm)], [c_42154, c_43101])).
% 24.36/13.64  tff(c_43133, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0 | u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42158, c_42720, c_43116])).
% 24.36/13.64  tff(c_43151, plain, (u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_43133])).
% 24.36/13.64  tff(c_42157, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_42144, c_85])).
% 24.36/13.64  tff(c_42151, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_42144, c_27334])).
% 24.36/13.64  tff(c_42170, plain, (v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_42144, c_40])).
% 24.36/13.64  tff(c_42190, plain, (v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_42170])).
% 24.36/13.64  tff(c_42176, plain, (l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_42144, c_190])).
% 24.36/13.64  tff(c_42194, plain, (l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_42176])).
% 24.36/13.64  tff(c_42155, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))))), inference(demodulation, [status(thm), theory('equality')], [c_42144, c_54])).
% 24.36/13.64  tff(c_42659, plain, (![D_3739, A_3740, B_3741]: (v5_pre_topc(D_3739, A_3740, g1_pre_topc(u1_struct_0(B_3741), u1_pre_topc(B_3741))) | ~v5_pre_topc(D_3739, A_3740, B_3741) | ~m1_subset_1(D_3739, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3740), u1_struct_0(g1_pre_topc(u1_struct_0(B_3741), u1_pre_topc(B_3741)))))) | ~v1_funct_2(D_3739, u1_struct_0(A_3740), u1_struct_0(g1_pre_topc(u1_struct_0(B_3741), u1_pre_topc(B_3741)))) | ~m1_subset_1(D_3739, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3740), u1_struct_0(B_3741)))) | ~v1_funct_2(D_3739, u1_struct_0(A_3740), u1_struct_0(B_3741)) | ~v1_funct_1(D_3739) | ~l1_pre_topc(B_3741) | ~v2_pre_topc(B_3741) | ~l1_pre_topc(A_3740) | ~v2_pre_topc(A_3740))), inference(cnfTransformation, [status(thm)], [f_151])).
% 24.36/13.64  tff(c_42662, plain, (v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_42155, c_42659])).
% 24.36/13.64  tff(c_42686, plain, (v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42190, c_42194, c_68, c_66, c_58, c_42158, c_42662])).
% 24.36/13.64  tff(c_42687, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_42151, c_42686])).
% 24.36/13.64  tff(c_44099, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42159, c_43151, c_42157, c_43151, c_42687])).
% 24.36/13.64  tff(c_42156, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_42144, c_121])).
% 24.36/13.64  tff(c_42534, plain, (![D_3724, A_3725, B_3726]: (v5_pre_topc(D_3724, g1_pre_topc(u1_struct_0(A_3725), u1_pre_topc(A_3725)), B_3726) | ~v5_pre_topc(D_3724, A_3725, B_3726) | ~m1_subset_1(D_3724, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_3725), u1_pre_topc(A_3725))), u1_struct_0(B_3726)))) | ~v1_funct_2(D_3724, u1_struct_0(g1_pre_topc(u1_struct_0(A_3725), u1_pre_topc(A_3725))), u1_struct_0(B_3726)) | ~m1_subset_1(D_3724, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3725), u1_struct_0(B_3726)))) | ~v1_funct_2(D_3724, u1_struct_0(A_3725), u1_struct_0(B_3726)) | ~v1_funct_1(D_3724) | ~l1_pre_topc(B_3726) | ~v2_pre_topc(B_3726) | ~l1_pre_topc(A_3725) | ~v2_pre_topc(A_3725))), inference(cnfTransformation, [status(thm)], [f_122])).
% 24.36/13.64  tff(c_44487, plain, (![A_3942, A_3943, B_3944]: (v5_pre_topc(A_3942, g1_pre_topc(u1_struct_0(A_3943), u1_pre_topc(A_3943)), B_3944) | ~v5_pre_topc(A_3942, A_3943, B_3944) | ~v1_funct_2(A_3942, u1_struct_0(g1_pre_topc(u1_struct_0(A_3943), u1_pre_topc(A_3943))), u1_struct_0(B_3944)) | ~m1_subset_1(A_3942, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3943), u1_struct_0(B_3944)))) | ~v1_funct_2(A_3942, u1_struct_0(A_3943), u1_struct_0(B_3944)) | ~v1_funct_1(A_3942) | ~l1_pre_topc(B_3944) | ~v2_pre_topc(B_3944) | ~l1_pre_topc(A_3943) | ~v2_pre_topc(A_3943) | ~r1_tarski(A_3942, k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_3943), u1_pre_topc(A_3943))), u1_struct_0(B_3944))))), inference(resolution, [status(thm)], [c_12, c_42534])).
% 24.36/13.64  tff(c_44520, plain, (![A_3942, B_3944]: (v5_pre_topc(A_3942, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_3944) | ~v5_pre_topc(A_3942, '#skF_1', B_3944) | ~v1_funct_2(A_3942, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_3944)) | ~m1_subset_1(A_3942, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_3944)))) | ~v1_funct_2(A_3942, u1_struct_0('#skF_1'), u1_struct_0(B_3944)) | ~v1_funct_1(A_3942) | ~l1_pre_topc(B_3944) | ~v2_pre_topc(B_3944) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(A_3942, k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(B_3944))))), inference(superposition, [status(thm), theory('equality')], [c_42144, c_44487])).
% 24.36/13.64  tff(c_49851, plain, (![A_4401, B_4402]: (v5_pre_topc(A_4401, g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), B_4402) | ~v5_pre_topc(A_4401, '#skF_1', B_4402) | ~m1_subset_1(A_4401, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_4402)))) | ~v1_funct_2(A_4401, k1_relat_1('#skF_4'), u1_struct_0(B_4402)) | ~v1_funct_1(A_4401) | ~l1_pre_topc(B_4402) | ~v2_pre_topc(B_4402) | ~r1_tarski(A_4401, k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_4402))))), inference(demodulation, [status(thm), theory('equality')], [c_43151, c_72, c_70, c_42144, c_42144, c_43151, c_42144, c_42144, c_44520])).
% 24.36/13.64  tff(c_49880, plain, (v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), '#skF_2') | ~v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~r1_tarski('#skF_4', k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_42157, c_49851])).
% 24.36/13.64  tff(c_49919, plain, (v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42156, c_68, c_66, c_58, c_42159, c_27271, c_49880])).
% 24.36/13.64  tff(c_49921, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44099, c_49919])).
% 24.36/13.64  tff(c_49922, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0), inference(splitRight, [status(thm)], [c_43133])).
% 24.36/13.64  tff(c_49946, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_49922, c_42158])).
% 24.36/13.64  tff(c_49945, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_49922, c_42155])).
% 24.36/13.64  tff(c_22, plain, (![C_17, A_15]: (k1_xboole_0=C_17 | ~v1_funct_2(C_17, A_15, k1_xboole_0) | k1_xboole_0=A_15 | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 24.36/13.64  tff(c_50043, plain, (k1_xboole_0='#skF_4' | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), k1_xboole_0) | u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))=k1_xboole_0), inference(resolution, [status(thm)], [c_49945, c_22])).
% 24.36/13.64  tff(c_50062, plain, (k1_xboole_0='#skF_4' | u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_49946, c_50043])).
% 24.36/13.64  tff(c_50066, plain, (u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))=k1_xboole_0), inference(splitLeft, [status(thm)], [c_50062])).
% 24.36/13.64  tff(c_49923, plain, (u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))!=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_43133])).
% 24.36/13.64  tff(c_50069, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50066, c_49923])).
% 24.36/13.64  tff(c_27395, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))))), inference(superposition, [status(thm), theory('equality')], [c_27297, c_16])).
% 24.36/13.64  tff(c_27405, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_27395])).
% 24.36/13.64  tff(c_42393, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_42144, c_27405])).
% 24.36/13.64  tff(c_42400, plain, (r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))))), inference(resolution, [status(thm)], [c_42393, c_10])).
% 24.36/13.64  tff(c_50071, plain, (r1_tarski(k1_relat_1('#skF_4'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_50066, c_42400])).
% 24.36/13.64  tff(c_50159, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_50071, c_113])).
% 24.36/13.64  tff(c_50165, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50069, c_50159])).
% 24.36/13.64  tff(c_50166, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_50062])).
% 24.36/13.64  tff(c_50200, plain, (![B_2431]: (v1_funct_2('#skF_4', '#skF_4', B_2431))), inference(demodulation, [status(thm), theory('equality')], [c_50166, c_50166, c_27541])).
% 24.36/13.64  tff(c_50204, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_50166, c_50166, c_27456])).
% 24.36/13.64  tff(c_50238, plain, (u1_struct_0('#skF_1')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_50204, c_42144])).
% 24.36/13.64  tff(c_42683, plain, (![A_3740, B_3741]: (v5_pre_topc(k1_xboole_0, A_3740, g1_pre_topc(u1_struct_0(B_3741), u1_pre_topc(B_3741))) | ~v5_pre_topc(k1_xboole_0, A_3740, B_3741) | ~v1_funct_2(k1_xboole_0, u1_struct_0(A_3740), u1_struct_0(g1_pre_topc(u1_struct_0(B_3741), u1_pre_topc(B_3741)))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3740), u1_struct_0(B_3741)))) | ~v1_funct_2(k1_xboole_0, u1_struct_0(A_3740), u1_struct_0(B_3741)) | ~v1_funct_1(k1_xboole_0) | ~l1_pre_topc(B_3741) | ~v2_pre_topc(B_3741) | ~l1_pre_topc(A_3740) | ~v2_pre_topc(A_3740))), inference(resolution, [status(thm)], [c_8, c_42659])).
% 24.36/13.64  tff(c_42696, plain, (![A_3740, B_3741]: (v5_pre_topc(k1_xboole_0, A_3740, g1_pre_topc(u1_struct_0(B_3741), u1_pre_topc(B_3741))) | ~v5_pre_topc(k1_xboole_0, A_3740, B_3741) | ~v1_funct_2(k1_xboole_0, u1_struct_0(A_3740), u1_struct_0(g1_pre_topc(u1_struct_0(B_3741), u1_pre_topc(B_3741)))) | ~v1_funct_2(k1_xboole_0, u1_struct_0(A_3740), u1_struct_0(B_3741)) | ~v1_funct_1(k1_xboole_0) | ~l1_pre_topc(B_3741) | ~v2_pre_topc(B_3741) | ~l1_pre_topc(A_3740) | ~v2_pre_topc(A_3740))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_42683])).
% 24.36/13.64  tff(c_50652, plain, (![A_4439, B_4440]: (v5_pre_topc('#skF_4', A_4439, g1_pre_topc(u1_struct_0(B_4440), u1_pre_topc(B_4440))) | ~v5_pre_topc('#skF_4', A_4439, B_4440) | ~v1_funct_2('#skF_4', u1_struct_0(A_4439), u1_struct_0(g1_pre_topc(u1_struct_0(B_4440), u1_pre_topc(B_4440)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_4439), u1_struct_0(B_4440)) | ~l1_pre_topc(B_4440) | ~v2_pre_topc(B_4440) | ~l1_pre_topc(A_4439) | ~v2_pre_topc(A_4439))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_50166, c_50166, c_50166, c_50166, c_50166, c_42696])).
% 24.36/13.64  tff(c_50655, plain, (![B_4440]: (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0(B_4440), u1_pre_topc(B_4440))) | ~v5_pre_topc('#skF_4', '#skF_1', B_4440) | ~v1_funct_2('#skF_4', '#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(B_4440), u1_pre_topc(B_4440)))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0(B_4440)) | ~l1_pre_topc(B_4440) | ~v2_pre_topc(B_4440) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_50238, c_50652])).
% 24.36/13.64  tff(c_50663, plain, (![B_4440]: (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0(B_4440), u1_pre_topc(B_4440))) | ~v5_pre_topc('#skF_4', '#skF_1', B_4440) | ~l1_pre_topc(B_4440) | ~v2_pre_topc(B_4440))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_50200, c_50238, c_50200, c_50655])).
% 24.36/13.64  tff(c_50219, plain, (~v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_50204, c_42151])).
% 24.36/13.64  tff(c_36, plain, (![A_19, B_20]: (v1_pre_topc(g1_pre_topc(A_19, B_20)) | ~m1_subset_1(B_20, k1_zfmisc_1(k1_zfmisc_1(A_19))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 24.36/13.64  tff(c_189, plain, (![A_84]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_84), u1_pre_topc(A_84))) | ~l1_pre_topc(A_84))), inference(resolution, [status(thm)], [c_179, c_36])).
% 24.36/13.64  tff(c_50004, plain, (v1_pre_topc(g1_pre_topc(k1_xboole_0, u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_49922, c_189])).
% 24.36/13.64  tff(c_51157, plain, (v1_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_50166, c_50004])).
% 24.36/13.64  tff(c_51158, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_51157])).
% 24.36/13.64  tff(c_51218, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_190, c_51158])).
% 24.36/13.64  tff(c_51224, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_51218])).
% 24.36/13.64  tff(c_51226, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_51157])).
% 24.36/13.64  tff(c_49995, plain, (v2_pre_topc(g1_pre_topc(k1_xboole_0, u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_49922, c_40])).
% 24.36/13.64  tff(c_52256, plain, (v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_51226, c_50166, c_49995])).
% 24.36/13.64  tff(c_52257, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_52256])).
% 24.36/13.64  tff(c_52263, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_40, c_52257])).
% 24.36/13.64  tff(c_52269, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_52263])).
% 24.36/13.64  tff(c_52271, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_52256])).
% 24.36/13.64  tff(c_50180, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50166, c_49946])).
% 24.36/13.64  tff(c_50628, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50204, c_50180])).
% 24.36/13.64  tff(c_50181, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_50166, c_49922])).
% 24.36/13.64  tff(c_42555, plain, (![A_3725, B_3726]: (v5_pre_topc(k1_xboole_0, g1_pre_topc(u1_struct_0(A_3725), u1_pre_topc(A_3725)), B_3726) | ~v5_pre_topc(k1_xboole_0, A_3725, B_3726) | ~v1_funct_2(k1_xboole_0, u1_struct_0(g1_pre_topc(u1_struct_0(A_3725), u1_pre_topc(A_3725))), u1_struct_0(B_3726)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3725), u1_struct_0(B_3726)))) | ~v1_funct_2(k1_xboole_0, u1_struct_0(A_3725), u1_struct_0(B_3726)) | ~v1_funct_1(k1_xboole_0) | ~l1_pre_topc(B_3726) | ~v2_pre_topc(B_3726) | ~l1_pre_topc(A_3725) | ~v2_pre_topc(A_3725))), inference(resolution, [status(thm)], [c_8, c_42534])).
% 24.36/13.64  tff(c_42564, plain, (![A_3725, B_3726]: (v5_pre_topc(k1_xboole_0, g1_pre_topc(u1_struct_0(A_3725), u1_pre_topc(A_3725)), B_3726) | ~v5_pre_topc(k1_xboole_0, A_3725, B_3726) | ~v1_funct_2(k1_xboole_0, u1_struct_0(g1_pre_topc(u1_struct_0(A_3725), u1_pre_topc(A_3725))), u1_struct_0(B_3726)) | ~v1_funct_2(k1_xboole_0, u1_struct_0(A_3725), u1_struct_0(B_3726)) | ~v1_funct_1(k1_xboole_0) | ~l1_pre_topc(B_3726) | ~v2_pre_topc(B_3726) | ~l1_pre_topc(A_3725) | ~v2_pre_topc(A_3725))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_42555])).
% 24.36/13.64  tff(c_50772, plain, (![A_4442, B_4443]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_4442), u1_pre_topc(A_4442)), B_4443) | ~v5_pre_topc('#skF_4', A_4442, B_4443) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_4442), u1_pre_topc(A_4442))), u1_struct_0(B_4443)) | ~v1_funct_2('#skF_4', u1_struct_0(A_4442), u1_struct_0(B_4443)) | ~l1_pre_topc(B_4443) | ~v2_pre_topc(B_4443) | ~l1_pre_topc(A_4442) | ~v2_pre_topc(A_4442))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_50166, c_50166, c_50166, c_50166, c_50166, c_42564])).
% 24.36/13.64  tff(c_50784, plain, (![B_4443]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_4443) | ~v5_pre_topc('#skF_4', '#skF_1', B_4443) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), u1_struct_0(B_4443)) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0(B_4443)) | ~l1_pre_topc(B_4443) | ~v2_pre_topc(B_4443) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_50238, c_50772])).
% 24.36/13.64  tff(c_53650, plain, (![B_4684]: (v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), B_4684) | ~v5_pre_topc('#skF_4', '#skF_1', B_4684) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), u1_struct_0(B_4684)) | ~l1_pre_topc(B_4684) | ~v2_pre_topc(B_4684))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_50200, c_50238, c_50238, c_50784])).
% 24.36/13.64  tff(c_53656, plain, (v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), '#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_50181, c_53650])).
% 24.36/13.64  tff(c_53662, plain, (v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_52271, c_51226, c_50628, c_53656])).
% 24.36/13.64  tff(c_53663, plain, (~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_50219, c_53662])).
% 24.36/13.64  tff(c_53669, plain, (~v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_50663, c_53663])).
% 24.36/13.64  tff(c_53676, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_27271, c_53669])).
% 24.36/13.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 24.36/13.64  
% 24.36/13.64  Inference rules
% 24.36/13.64  ----------------------
% 24.36/13.64  #Ref     : 0
% 24.36/13.64  #Sup     : 10424
% 24.36/13.64  #Fact    : 0
% 24.36/13.64  #Define  : 0
% 24.36/13.64  #Split   : 81
% 24.36/13.64  #Chain   : 0
% 24.36/13.64  #Close   : 0
% 24.36/13.64  
% 24.36/13.64  Ordering : KBO
% 24.36/13.64  
% 24.36/13.64  Simplification rules
% 24.36/13.64  ----------------------
% 24.36/13.64  #Subsume      : 1927
% 24.36/13.64  #Demod        : 28763
% 24.36/13.64  #Tautology    : 3714
% 24.36/13.64  #SimpNegUnit  : 193
% 24.36/13.64  #BackRed      : 483
% 24.36/13.64  
% 24.36/13.64  #Partial instantiations: 0
% 24.36/13.64  #Strategies tried      : 1
% 24.36/13.64  
% 24.36/13.64  Timing (in seconds)
% 24.36/13.64  ----------------------
% 24.36/13.64  Preprocessing        : 0.38
% 24.36/13.64  Parsing              : 0.20
% 24.36/13.64  CNF conversion       : 0.03
% 24.36/13.64  Main loop            : 12.29
% 24.36/13.64  Inferencing          : 2.97
% 24.36/13.64  Reduction            : 5.87
% 24.36/13.64  Demodulation         : 4.98
% 24.36/13.64  BG Simplification    : 0.33
% 24.36/13.64  Subsumption          : 2.56
% 24.36/13.64  Abstraction          : 0.57
% 24.36/13.64  MUC search           : 0.00
% 24.36/13.64  Cooper               : 0.00
% 24.36/13.64  Total                : 12.83
% 24.36/13.64  Index Insertion      : 0.00
% 24.36/13.64  Index Deletion       : 0.00
% 24.36/13.64  Index Matching       : 0.00
% 24.36/13.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
