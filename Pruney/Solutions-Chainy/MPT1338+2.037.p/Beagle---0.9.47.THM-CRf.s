%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:19 EST 2020

% Result     : Theorem 4.11s
% Output     : CNFRefutation 4.40s
% Verified   : 
% Statistics : Number of formulae       :  188 (115696 expanded)
%              Number of leaves         :   47 (40733 expanded)
%              Depth                    :   29
%              Number of atoms          :  325 (363295 expanded)
%              Number of equality atoms :  132 (135948 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_zfmisc_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k3_tarski > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_subset_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

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

tff(f_172,negated_conjecture,(
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

tff(f_42,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_44,axiom,(
    ! [A] : v1_xboole_0(k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_subset_1)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_57,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_47,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_27,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_104,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v1_zfmisc_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc20_struct_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_124,axiom,(
    ! [A] :
      ( ~ ( ? [B] :
              ( B != k1_xboole_0
              & r2_hidden(B,A) )
          & k3_tarski(A) = k1_xboole_0 )
      & ~ ( k3_tarski(A) != k1_xboole_0
          & ! [B] :
              ~ ( B != k1_xboole_0
                & r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_orders_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_87,axiom,(
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

tff(f_136,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_148,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_tops_2(A,B,C))
        & v1_funct_2(k2_tops_2(A,B,C),B,A)
        & m1_subset_1(k2_tops_2(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_74,plain,(
    l1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_12,plain,(
    ! [A_4] : k1_subset_1(A_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_14,plain,(
    ! [A_5] : v1_xboole_0(k1_subset_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_79,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_14])).

tff(c_78,plain,(
    l1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_112,plain,(
    ! [A_41] :
      ( u1_struct_0(A_41) = k2_struct_0(A_41)
      | ~ l1_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_120,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_112])).

tff(c_119,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_112])).

tff(c_68,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_134,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_119,c_68])).

tff(c_151,plain,(
    ! [C_50,A_51,B_52] :
      ( v1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_160,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_134,c_151])).

tff(c_72,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_64,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_18,plain,(
    ! [A_7] :
      ( k2_relat_1(k2_funct_1(A_7)) = k1_relat_1(A_7)
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1280,plain,(
    ! [A_131,B_132,C_133] :
      ( k2_relset_1(A_131,B_132,C_133) = k2_relat_1(C_133)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1296,plain,(
    k2_relset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'),'#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_134,c_1280])).

tff(c_66,plain,(
    k2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') = k2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_146,plain,(
    k2_relset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'),'#skF_5') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_119,c_66])).

tff(c_1297,plain,(
    k2_struct_0('#skF_4') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1296,c_146])).

tff(c_16,plain,(
    ! [A_6] : ~ v1_xboole_0(k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [A_1] : k3_tarski(k1_zfmisc_1(A_1)) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1193,plain,(
    ! [A_122] :
      ( m1_subset_1('#skF_1'(A_122),k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ l1_struct_0(A_122)
      | v2_struct_0(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1202,plain,
    ( m1_subset_1('#skF_1'('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_1193])).

tff(c_1207,plain,
    ( m1_subset_1('#skF_1'('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1202])).

tff(c_1208,plain,(
    m1_subset_1('#skF_1'('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1207])).

tff(c_6,plain,(
    ! [B_3,A_2] :
      ( r2_hidden(B_3,A_2)
      | ~ m1_subset_1(B_3,A_2)
      | v1_xboole_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_171,plain,(
    ! [A_57,B_58] :
      ( k3_tarski(A_57) != k1_xboole_0
      | ~ r2_hidden(B_58,A_57)
      | k1_xboole_0 = B_58 ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1223,plain,(
    ! [A_124,B_125] :
      ( k3_tarski(A_124) != k1_xboole_0
      | k1_xboole_0 = B_125
      | ~ m1_subset_1(B_125,A_124)
      | v1_xboole_0(A_124) ) ),
    inference(resolution,[status(thm)],[c_6,c_171])).

tff(c_1226,plain,
    ( k3_tarski(k1_zfmisc_1(k2_struct_0('#skF_4'))) != k1_xboole_0
    | '#skF_1'('#skF_4') = k1_xboole_0
    | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_1208,c_1223])).

tff(c_1240,plain,
    ( k2_struct_0('#skF_4') != k1_xboole_0
    | '#skF_1'('#skF_4') = k1_xboole_0
    | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1226])).

tff(c_1241,plain,
    ( k2_struct_0('#skF_4') != k1_xboole_0
    | '#skF_1'('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_1240])).

tff(c_1250,plain,(
    k2_struct_0('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1241])).

tff(c_1304,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1297,c_1250])).

tff(c_70,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_121,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_70])).

tff(c_132,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_3'),k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_121])).

tff(c_1308,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_3'),k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1297,c_132])).

tff(c_1307,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'),k2_relat_1('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1297,c_134])).

tff(c_24,plain,(
    ! [A_11,B_12,C_13] :
      ( k1_relset_1(A_11,B_12,C_13) = k1_relat_1(C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1363,plain,(
    k1_relset_1(k2_struct_0('#skF_3'),k2_relat_1('#skF_5'),'#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1307,c_24])).

tff(c_1443,plain,(
    ! [B_146,A_147,C_148] :
      ( k1_xboole_0 = B_146
      | k1_relset_1(A_147,B_146,C_148) = A_147
      | ~ v1_funct_2(C_148,A_147,B_146)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(A_147,B_146))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1446,plain,
    ( k2_relat_1('#skF_5') = k1_xboole_0
    | k1_relset_1(k2_struct_0('#skF_3'),k2_relat_1('#skF_5'),'#skF_5') = k2_struct_0('#skF_3')
    | ~ v1_funct_2('#skF_5',k2_struct_0('#skF_3'),k2_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_1307,c_1443])).

tff(c_1457,plain,
    ( k2_relat_1('#skF_5') = k1_xboole_0
    | k2_struct_0('#skF_3') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1308,c_1363,c_1446])).

tff(c_1458,plain,(
    k2_struct_0('#skF_3') = k1_relat_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_1304,c_1457])).

tff(c_1469,plain,(
    v1_funct_2('#skF_5',k1_relat_1('#skF_5'),k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1458,c_1308])).

tff(c_1467,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1458,c_1307])).

tff(c_1302,plain,(
    k2_relset_1(k2_struct_0('#skF_3'),k2_relat_1('#skF_5'),'#skF_5') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1297,c_1296])).

tff(c_1466,plain,(
    k2_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1458,c_1302])).

tff(c_1665,plain,(
    ! [A_166,B_167,C_168] :
      ( k2_tops_2(A_166,B_167,C_168) = k2_funct_1(C_168)
      | ~ v2_funct_1(C_168)
      | k2_relset_1(A_166,B_167,C_168) != B_167
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(A_166,B_167)))
      | ~ v1_funct_2(C_168,A_166,B_167)
      | ~ v1_funct_1(C_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1671,plain,
    ( k2_tops_2(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5') = k2_funct_1('#skF_5')
    | ~ v2_funct_1('#skF_5')
    | k2_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5') != k2_relat_1('#skF_5')
    | ~ v1_funct_2('#skF_5',k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1467,c_1665])).

tff(c_1683,plain,(
    k2_tops_2(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5') = k2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1469,c_1466,c_64,c_1671])).

tff(c_56,plain,(
    ! [A_30,B_31,C_32] :
      ( m1_subset_1(k2_tops_2(A_30,B_31,C_32),k1_zfmisc_1(k2_zfmisc_1(B_31,A_30)))
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31)))
      | ~ v1_funct_2(C_32,A_30,B_31)
      | ~ v1_funct_1(C_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_1696,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_5'),k1_relat_1('#skF_5'))))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))))
    | ~ v1_funct_2('#skF_5',k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1683,c_56])).

tff(c_1700,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_5'),k1_relat_1('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1469,c_1467,c_1696])).

tff(c_26,plain,(
    ! [A_14,B_15,C_16] :
      ( k2_relset_1(A_14,B_15,C_16) = k2_relat_1(C_16)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1798,plain,(
    k2_relset_1(k2_relat_1('#skF_5'),k1_relat_1('#skF_5'),k2_funct_1('#skF_5')) = k2_relat_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_1700,c_26])).

tff(c_270,plain,(
    ! [A_68,B_69,C_70] :
      ( k2_relset_1(A_68,B_69,C_70) = k2_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_286,plain,(
    k2_relset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'),'#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_134,c_270])).

tff(c_287,plain,(
    k2_struct_0('#skF_4') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_146])).

tff(c_194,plain,(
    ! [A_60] :
      ( m1_subset_1('#skF_1'(A_60),k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_struct_0(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_203,plain,
    ( m1_subset_1('#skF_1'('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_194])).

tff(c_208,plain,
    ( m1_subset_1('#skF_1'('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_203])).

tff(c_209,plain,(
    m1_subset_1('#skF_1'('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_208])).

tff(c_224,plain,(
    ! [A_62,B_63] :
      ( k3_tarski(A_62) != k1_xboole_0
      | k1_xboole_0 = B_63
      | ~ m1_subset_1(B_63,A_62)
      | v1_xboole_0(A_62) ) ),
    inference(resolution,[status(thm)],[c_6,c_171])).

tff(c_227,plain,
    ( k3_tarski(k1_zfmisc_1(k2_struct_0('#skF_4'))) != k1_xboole_0
    | '#skF_1'('#skF_4') = k1_xboole_0
    | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_209,c_224])).

tff(c_241,plain,
    ( k2_struct_0('#skF_4') != k1_xboole_0
    | '#skF_1'('#skF_4') = k1_xboole_0
    | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_227])).

tff(c_242,plain,
    ( k2_struct_0('#skF_4') != k1_xboole_0
    | '#skF_1'('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_241])).

tff(c_251,plain,(
    k2_struct_0('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_242])).

tff(c_295,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_287,c_251])).

tff(c_298,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_3'),k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_287,c_132])).

tff(c_297,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'),k2_relat_1('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_287,c_134])).

tff(c_357,plain,(
    k1_relset_1(k2_struct_0('#skF_3'),k2_relat_1('#skF_5'),'#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_297,c_24])).

tff(c_435,plain,(
    ! [B_84,A_85,C_86] :
      ( k1_xboole_0 = B_84
      | k1_relset_1(A_85,B_84,C_86) = A_85
      | ~ v1_funct_2(C_86,A_85,B_84)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_85,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_438,plain,
    ( k2_relat_1('#skF_5') = k1_xboole_0
    | k1_relset_1(k2_struct_0('#skF_3'),k2_relat_1('#skF_5'),'#skF_5') = k2_struct_0('#skF_3')
    | ~ v1_funct_2('#skF_5',k2_struct_0('#skF_3'),k2_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_297,c_435])).

tff(c_449,plain,
    ( k2_relat_1('#skF_5') = k1_xboole_0
    | k2_struct_0('#skF_3') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_357,c_438])).

tff(c_450,plain,(
    k2_struct_0('#skF_3') = k1_relat_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_295,c_449])).

tff(c_479,plain,(
    v1_funct_2('#skF_5',k1_relat_1('#skF_5'),k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_450,c_298])).

tff(c_292,plain,(
    k2_relset_1(k2_struct_0('#skF_3'),k2_relat_1('#skF_5'),'#skF_5') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_287,c_286])).

tff(c_477,plain,(
    k2_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_450,c_292])).

tff(c_476,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_450,c_297])).

tff(c_661,plain,(
    ! [A_105,B_106,C_107] :
      ( k2_tops_2(A_105,B_106,C_107) = k2_funct_1(C_107)
      | ~ v2_funct_1(C_107)
      | k2_relset_1(A_105,B_106,C_107) != B_106
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106)))
      | ~ v1_funct_2(C_107,A_105,B_106)
      | ~ v1_funct_1(C_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_667,plain,
    ( k2_tops_2(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5') = k2_funct_1('#skF_5')
    | ~ v2_funct_1('#skF_5')
    | k2_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5') != k2_relat_1('#skF_5')
    | ~ v1_funct_2('#skF_5',k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_476,c_661])).

tff(c_679,plain,(
    k2_tops_2(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5') = k2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_479,c_477,c_64,c_667])).

tff(c_62,plain,
    ( k2_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')) != k2_struct_0('#skF_3')
    | k1_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')) != k2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_180,plain,
    ( k2_relset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_3'),k2_tops_2(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'),'#skF_5')) != k2_struct_0('#skF_3')
    | k1_relset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_3'),k2_tops_2(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'),'#skF_5')) != k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_120,c_119,c_119,c_120,c_120,c_119,c_119,c_62])).

tff(c_181,plain,(
    k1_relset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_3'),k2_tops_2(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'),'#skF_5')) != k2_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_180])).

tff(c_294,plain,(
    k1_relset_1(k2_relat_1('#skF_5'),k2_struct_0('#skF_3'),k2_tops_2(k2_struct_0('#skF_3'),k2_relat_1('#skF_5'),'#skF_5')) != k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_287,c_287,c_287,c_181])).

tff(c_474,plain,(
    k1_relset_1(k2_relat_1('#skF_5'),k1_relat_1('#skF_5'),k2_tops_2(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5')) != k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_450,c_450,c_294])).

tff(c_685,plain,(
    k1_relset_1(k2_relat_1('#skF_5'),k1_relat_1('#skF_5'),k2_funct_1('#skF_5')) != k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_679,c_474])).

tff(c_546,plain,(
    ! [A_90,B_91,C_92] :
      ( v1_funct_2(k2_tops_2(A_90,B_91,C_92),B_91,A_90)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91)))
      | ~ v1_funct_2(C_92,A_90,B_91)
      | ~ v1_funct_1(C_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_548,plain,
    ( v1_funct_2(k2_tops_2(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5'),k2_relat_1('#skF_5'),k1_relat_1('#skF_5'))
    | ~ v1_funct_2('#skF_5',k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_476,c_546])).

tff(c_557,plain,(
    v1_funct_2(k2_tops_2(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5'),k2_relat_1('#skF_5'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_479,c_548])).

tff(c_686,plain,(
    v1_funct_2(k2_funct_1('#skF_5'),k2_relat_1('#skF_5'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_679,c_557])).

tff(c_691,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_5'),k1_relat_1('#skF_5'))))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))))
    | ~ v1_funct_2('#skF_5',k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_679,c_56])).

tff(c_695,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_5'),k1_relat_1('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_479,c_476,c_691])).

tff(c_38,plain,(
    ! [B_18,A_17,C_19] :
      ( k1_xboole_0 = B_18
      | k1_relset_1(A_17,B_18,C_19) = A_17
      | ~ v1_funct_2(C_19,A_17,B_18)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_731,plain,
    ( k1_relat_1('#skF_5') = k1_xboole_0
    | k1_relset_1(k2_relat_1('#skF_5'),k1_relat_1('#skF_5'),k2_funct_1('#skF_5')) = k2_relat_1('#skF_5')
    | ~ v1_funct_2(k2_funct_1('#skF_5'),k2_relat_1('#skF_5'),k1_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_695,c_38])).

tff(c_767,plain,
    ( k1_relat_1('#skF_5') = k1_xboole_0
    | k1_relset_1(k2_relat_1('#skF_5'),k1_relat_1('#skF_5'),k2_funct_1('#skF_5')) = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_686,c_731])).

tff(c_768,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_685,c_767])).

tff(c_781,plain,(
    v1_funct_2(k2_funct_1('#skF_5'),k2_relat_1('#skF_5'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_768,c_686])).

tff(c_779,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_5'),k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_768,c_695])).

tff(c_30,plain,(
    ! [C_19,A_17] :
      ( k1_xboole_0 = C_19
      | ~ v1_funct_2(C_19,A_17,k1_xboole_0)
      | k1_xboole_0 = A_17
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_942,plain,
    ( k2_funct_1('#skF_5') = k1_xboole_0
    | ~ v1_funct_2(k2_funct_1('#skF_5'),k2_relat_1('#skF_5'),k1_xboole_0)
    | k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_779,c_30])).

tff(c_985,plain,
    ( k2_funct_1('#skF_5') = k1_xboole_0
    | k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_781,c_942])).

tff(c_986,plain,(
    k2_funct_1('#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_295,c_985])).

tff(c_20,plain,(
    ! [A_7] :
      ( k1_relat_1(k2_funct_1(A_7)) = k2_relat_1(A_7)
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1012,plain,
    ( k2_relat_1('#skF_5') = k1_relat_1(k1_xboole_0)
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_986,c_20])).

tff(c_1019,plain,(
    k2_relat_1('#skF_5') = k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_72,c_64,c_1012])).

tff(c_780,plain,(
    k1_relset_1(k2_relat_1('#skF_5'),k1_xboole_0,k2_funct_1('#skF_5')) != k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_768,c_685])).

tff(c_1002,plain,(
    k1_relset_1(k2_relat_1('#skF_5'),k1_xboole_0,k1_xboole_0) != k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_986,c_780])).

tff(c_1106,plain,(
    k1_relset_1(k1_relat_1(k1_xboole_0),k1_xboole_0,k1_xboole_0) != k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1019,c_1019,c_1002])).

tff(c_787,plain,(
    v1_funct_2('#skF_5',k1_xboole_0,k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_768,c_479])).

tff(c_1037,plain,(
    v1_funct_2('#skF_5',k1_xboole_0,k1_relat_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1019,c_787])).

tff(c_782,plain,(
    k2_tops_2(k1_xboole_0,k2_relat_1('#skF_5'),'#skF_5') = k2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_768,c_679])).

tff(c_1005,plain,(
    k2_tops_2(k1_xboole_0,k2_relat_1('#skF_5'),'#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_986,c_782])).

tff(c_1073,plain,(
    k2_tops_2(k1_xboole_0,k1_relat_1(k1_xboole_0),'#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1019,c_1005])).

tff(c_786,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_768,c_476])).

tff(c_1038,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(k1_xboole_0)))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1019,c_786])).

tff(c_584,plain,(
    ! [A_98,B_99,C_100] :
      ( m1_subset_1(k2_tops_2(A_98,B_99,C_100),k1_zfmisc_1(k2_zfmisc_1(B_99,A_98)))
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99)))
      | ~ v1_funct_2(C_100,A_98,B_99)
      | ~ v1_funct_1(C_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_630,plain,(
    ! [B_99,A_98,C_100] :
      ( k1_relset_1(B_99,A_98,k2_tops_2(A_98,B_99,C_100)) = k1_relat_1(k2_tops_2(A_98,B_99,C_100))
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99)))
      | ~ v1_funct_2(C_100,A_98,B_99)
      | ~ v1_funct_1(C_100) ) ),
    inference(resolution,[status(thm)],[c_584,c_24])).

tff(c_1108,plain,
    ( k1_relset_1(k1_relat_1(k1_xboole_0),k1_xboole_0,k2_tops_2(k1_xboole_0,k1_relat_1(k1_xboole_0),'#skF_5')) = k1_relat_1(k2_tops_2(k1_xboole_0,k1_relat_1(k1_xboole_0),'#skF_5'))
    | ~ v1_funct_2('#skF_5',k1_xboole_0,k1_relat_1(k1_xboole_0))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1038,c_630])).

tff(c_1151,plain,(
    k1_relset_1(k1_relat_1(k1_xboole_0),k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1037,c_1073,c_1073,c_1108])).

tff(c_1153,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1106,c_1151])).

tff(c_1154,plain,(
    '#skF_1'('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_242])).

tff(c_44,plain,(
    ! [A_21] :
      ( ~ v1_xboole_0('#skF_1'(A_21))
      | ~ l1_struct_0(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1166,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1154,c_44])).

tff(c_1176,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_79,c_1166])).

tff(c_1178,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1176])).

tff(c_1179,plain,(
    k2_relset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_3'),k2_tops_2(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'),'#skF_5')) != k2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_180])).

tff(c_1375,plain,(
    k2_relset_1(k2_relat_1('#skF_5'),k2_struct_0('#skF_3'),k2_tops_2(k2_struct_0('#skF_3'),k2_relat_1('#skF_5'),'#skF_5')) != k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1297,c_1297,c_1179])).

tff(c_1465,plain,(
    k2_relset_1(k2_relat_1('#skF_5'),k1_relat_1('#skF_5'),k2_tops_2(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5')) != k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1458,c_1458,c_1458,c_1375])).

tff(c_1691,plain,(
    k2_relset_1(k2_relat_1('#skF_5'),k1_relat_1('#skF_5'),k2_funct_1('#skF_5')) != k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1683,c_1465])).

tff(c_1805,plain,(
    k2_relat_1(k2_funct_1('#skF_5')) != k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1798,c_1691])).

tff(c_1812,plain,
    ( ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1805])).

tff(c_1816,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_72,c_64,c_1812])).

tff(c_1817,plain,(
    '#skF_1'('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1241])).

tff(c_1829,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1817,c_44])).

tff(c_1839,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_79,c_1829])).

tff(c_1841,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1839])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:53:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.11/1.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.16/1.80  
% 4.16/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.16/1.80  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_zfmisc_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k3_tarski > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_subset_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 4.16/1.80  
% 4.16/1.80  %Foreground sorts:
% 4.16/1.80  
% 4.16/1.80  
% 4.16/1.80  %Background operators:
% 4.16/1.80  
% 4.16/1.80  
% 4.16/1.80  %Foreground operators:
% 4.16/1.80  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.16/1.80  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.16/1.80  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.16/1.80  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.16/1.80  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.16/1.80  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.16/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.16/1.80  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.16/1.80  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.16/1.80  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.16/1.80  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.16/1.80  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 4.16/1.80  tff('#skF_5', type, '#skF_5': $i).
% 4.16/1.80  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.16/1.80  tff('#skF_3', type, '#skF_3': $i).
% 4.16/1.80  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.16/1.80  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.16/1.80  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.16/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.16/1.80  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.16/1.80  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.16/1.80  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.16/1.80  tff('#skF_4', type, '#skF_4': $i).
% 4.16/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.16/1.80  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 4.16/1.80  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 4.16/1.80  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.16/1.80  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.16/1.80  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.16/1.80  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.16/1.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.16/1.80  
% 4.40/1.83  tff(f_172, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_2)).
% 4.40/1.83  tff(f_42, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 4.40/1.83  tff(f_44, axiom, (![A]: v1_xboole_0(k1_subset_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc13_subset_1)).
% 4.40/1.83  tff(f_91, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 4.40/1.83  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.40/1.83  tff(f_57, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 4.40/1.83  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.40/1.83  tff(f_47, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 4.40/1.83  tff(f_27, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 4.40/1.83  tff(f_104, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (?[B]: ((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v1_zfmisc_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc20_struct_0)).
% 4.40/1.83  tff(f_40, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 4.40/1.83  tff(f_124, axiom, (![A]: (~((?[B]: (~(B = k1_xboole_0) & r2_hidden(B, A))) & (k3_tarski(A) = k1_xboole_0)) & ~(~(k3_tarski(A) = k1_xboole_0) & (![B]: ~(~(B = k1_xboole_0) & r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_orders_1)).
% 4.40/1.83  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.40/1.83  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.40/1.83  tff(f_136, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 4.40/1.83  tff(f_148, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v1_funct_1(k2_tops_2(A, B, C)) & v1_funct_2(k2_tops_2(A, B, C), B, A)) & m1_subset_1(k2_tops_2(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_2)).
% 4.40/1.83  tff(c_76, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_172])).
% 4.40/1.83  tff(c_74, plain, (l1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_172])).
% 4.40/1.83  tff(c_12, plain, (![A_4]: (k1_subset_1(A_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.40/1.83  tff(c_14, plain, (![A_5]: (v1_xboole_0(k1_subset_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.40/1.83  tff(c_79, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_14])).
% 4.40/1.83  tff(c_78, plain, (l1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_172])).
% 4.40/1.83  tff(c_112, plain, (![A_41]: (u1_struct_0(A_41)=k2_struct_0(A_41) | ~l1_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.40/1.83  tff(c_120, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_78, c_112])).
% 4.40/1.83  tff(c_119, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_74, c_112])).
% 4.40/1.83  tff(c_68, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_172])).
% 4.40/1.83  tff(c_134, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_119, c_68])).
% 4.40/1.83  tff(c_151, plain, (![C_50, A_51, B_52]: (v1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.40/1.83  tff(c_160, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_134, c_151])).
% 4.40/1.83  tff(c_72, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_172])).
% 4.40/1.83  tff(c_64, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_172])).
% 4.40/1.83  tff(c_18, plain, (![A_7]: (k2_relat_1(k2_funct_1(A_7))=k1_relat_1(A_7) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.40/1.83  tff(c_1280, plain, (![A_131, B_132, C_133]: (k2_relset_1(A_131, B_132, C_133)=k2_relat_1(C_133) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.40/1.83  tff(c_1296, plain, (k2_relset_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'), '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_134, c_1280])).
% 4.40/1.83  tff(c_66, plain, (k2_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5')=k2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_172])).
% 4.40/1.83  tff(c_146, plain, (k2_relset_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'), '#skF_5')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_119, c_66])).
% 4.40/1.83  tff(c_1297, plain, (k2_struct_0('#skF_4')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1296, c_146])).
% 4.40/1.83  tff(c_16, plain, (![A_6]: (~v1_xboole_0(k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.40/1.83  tff(c_2, plain, (![A_1]: (k3_tarski(k1_zfmisc_1(A_1))=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.40/1.83  tff(c_1193, plain, (![A_122]: (m1_subset_1('#skF_1'(A_122), k1_zfmisc_1(u1_struct_0(A_122))) | ~l1_struct_0(A_122) | v2_struct_0(A_122))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.40/1.83  tff(c_1202, plain, (m1_subset_1('#skF_1'('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_119, c_1193])).
% 4.40/1.83  tff(c_1207, plain, (m1_subset_1('#skF_1'('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1202])).
% 4.40/1.83  tff(c_1208, plain, (m1_subset_1('#skF_1'('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_76, c_1207])).
% 4.40/1.83  tff(c_6, plain, (![B_3, A_2]: (r2_hidden(B_3, A_2) | ~m1_subset_1(B_3, A_2) | v1_xboole_0(A_2))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.40/1.83  tff(c_171, plain, (![A_57, B_58]: (k3_tarski(A_57)!=k1_xboole_0 | ~r2_hidden(B_58, A_57) | k1_xboole_0=B_58)), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.40/1.83  tff(c_1223, plain, (![A_124, B_125]: (k3_tarski(A_124)!=k1_xboole_0 | k1_xboole_0=B_125 | ~m1_subset_1(B_125, A_124) | v1_xboole_0(A_124))), inference(resolution, [status(thm)], [c_6, c_171])).
% 4.40/1.83  tff(c_1226, plain, (k3_tarski(k1_zfmisc_1(k2_struct_0('#skF_4')))!=k1_xboole_0 | '#skF_1'('#skF_4')=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_1208, c_1223])).
% 4.40/1.83  tff(c_1240, plain, (k2_struct_0('#skF_4')!=k1_xboole_0 | '#skF_1'('#skF_4')=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1226])).
% 4.40/1.83  tff(c_1241, plain, (k2_struct_0('#skF_4')!=k1_xboole_0 | '#skF_1'('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_16, c_1240])).
% 4.40/1.83  tff(c_1250, plain, (k2_struct_0('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1241])).
% 4.40/1.83  tff(c_1304, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1297, c_1250])).
% 4.40/1.83  tff(c_70, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_172])).
% 4.40/1.83  tff(c_121, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_3'), k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_70])).
% 4.40/1.83  tff(c_132, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_3'), k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_121])).
% 4.40/1.83  tff(c_1308, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_3'), k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1297, c_132])).
% 4.40/1.83  tff(c_1307, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'), k2_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_1297, c_134])).
% 4.40/1.83  tff(c_24, plain, (![A_11, B_12, C_13]: (k1_relset_1(A_11, B_12, C_13)=k1_relat_1(C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.40/1.83  tff(c_1363, plain, (k1_relset_1(k2_struct_0('#skF_3'), k2_relat_1('#skF_5'), '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1307, c_24])).
% 4.40/1.83  tff(c_1443, plain, (![B_146, A_147, C_148]: (k1_xboole_0=B_146 | k1_relset_1(A_147, B_146, C_148)=A_147 | ~v1_funct_2(C_148, A_147, B_146) | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1(A_147, B_146))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.40/1.83  tff(c_1446, plain, (k2_relat_1('#skF_5')=k1_xboole_0 | k1_relset_1(k2_struct_0('#skF_3'), k2_relat_1('#skF_5'), '#skF_5')=k2_struct_0('#skF_3') | ~v1_funct_2('#skF_5', k2_struct_0('#skF_3'), k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_1307, c_1443])).
% 4.40/1.83  tff(c_1457, plain, (k2_relat_1('#skF_5')=k1_xboole_0 | k2_struct_0('#skF_3')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1308, c_1363, c_1446])).
% 4.40/1.83  tff(c_1458, plain, (k2_struct_0('#skF_3')=k1_relat_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_1304, c_1457])).
% 4.40/1.83  tff(c_1469, plain, (v1_funct_2('#skF_5', k1_relat_1('#skF_5'), k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1458, c_1308])).
% 4.40/1.83  tff(c_1467, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_1458, c_1307])).
% 4.40/1.83  tff(c_1302, plain, (k2_relset_1(k2_struct_0('#skF_3'), k2_relat_1('#skF_5'), '#skF_5')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1297, c_1296])).
% 4.40/1.83  tff(c_1466, plain, (k2_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1458, c_1302])).
% 4.40/1.83  tff(c_1665, plain, (![A_166, B_167, C_168]: (k2_tops_2(A_166, B_167, C_168)=k2_funct_1(C_168) | ~v2_funct_1(C_168) | k2_relset_1(A_166, B_167, C_168)!=B_167 | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))) | ~v1_funct_2(C_168, A_166, B_167) | ~v1_funct_1(C_168))), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.40/1.83  tff(c_1671, plain, (k2_tops_2(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5')=k2_funct_1('#skF_5') | ~v2_funct_1('#skF_5') | k2_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5')!=k2_relat_1('#skF_5') | ~v1_funct_2('#skF_5', k1_relat_1('#skF_5'), k2_relat_1('#skF_5')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_1467, c_1665])).
% 4.40/1.83  tff(c_1683, plain, (k2_tops_2(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5')=k2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1469, c_1466, c_64, c_1671])).
% 4.40/1.83  tff(c_56, plain, (![A_30, B_31, C_32]: (m1_subset_1(k2_tops_2(A_30, B_31, C_32), k1_zfmisc_1(k2_zfmisc_1(B_31, A_30))) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))) | ~v1_funct_2(C_32, A_30, B_31) | ~v1_funct_1(C_32))), inference(cnfTransformation, [status(thm)], [f_148])).
% 4.40/1.83  tff(c_1696, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_5'), k1_relat_1('#skF_5')))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5')))) | ~v1_funct_2('#skF_5', k1_relat_1('#skF_5'), k2_relat_1('#skF_5')) | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1683, c_56])).
% 4.40/1.83  tff(c_1700, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_5'), k1_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1469, c_1467, c_1696])).
% 4.40/1.83  tff(c_26, plain, (![A_14, B_15, C_16]: (k2_relset_1(A_14, B_15, C_16)=k2_relat_1(C_16) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.40/1.83  tff(c_1798, plain, (k2_relset_1(k2_relat_1('#skF_5'), k1_relat_1('#skF_5'), k2_funct_1('#skF_5'))=k2_relat_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_1700, c_26])).
% 4.40/1.83  tff(c_270, plain, (![A_68, B_69, C_70]: (k2_relset_1(A_68, B_69, C_70)=k2_relat_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.40/1.83  tff(c_286, plain, (k2_relset_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'), '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_134, c_270])).
% 4.40/1.83  tff(c_287, plain, (k2_struct_0('#skF_4')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_286, c_146])).
% 4.40/1.83  tff(c_194, plain, (![A_60]: (m1_subset_1('#skF_1'(A_60), k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_struct_0(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.40/1.83  tff(c_203, plain, (m1_subset_1('#skF_1'('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_119, c_194])).
% 4.40/1.83  tff(c_208, plain, (m1_subset_1('#skF_1'('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_203])).
% 4.40/1.83  tff(c_209, plain, (m1_subset_1('#skF_1'('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_76, c_208])).
% 4.40/1.83  tff(c_224, plain, (![A_62, B_63]: (k3_tarski(A_62)!=k1_xboole_0 | k1_xboole_0=B_63 | ~m1_subset_1(B_63, A_62) | v1_xboole_0(A_62))), inference(resolution, [status(thm)], [c_6, c_171])).
% 4.40/1.83  tff(c_227, plain, (k3_tarski(k1_zfmisc_1(k2_struct_0('#skF_4')))!=k1_xboole_0 | '#skF_1'('#skF_4')=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_209, c_224])).
% 4.40/1.83  tff(c_241, plain, (k2_struct_0('#skF_4')!=k1_xboole_0 | '#skF_1'('#skF_4')=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_227])).
% 4.40/1.83  tff(c_242, plain, (k2_struct_0('#skF_4')!=k1_xboole_0 | '#skF_1'('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_16, c_241])).
% 4.40/1.83  tff(c_251, plain, (k2_struct_0('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_242])).
% 4.40/1.83  tff(c_295, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_287, c_251])).
% 4.40/1.83  tff(c_298, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_3'), k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_287, c_132])).
% 4.40/1.83  tff(c_297, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'), k2_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_287, c_134])).
% 4.40/1.83  tff(c_357, plain, (k1_relset_1(k2_struct_0('#skF_3'), k2_relat_1('#skF_5'), '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_297, c_24])).
% 4.40/1.83  tff(c_435, plain, (![B_84, A_85, C_86]: (k1_xboole_0=B_84 | k1_relset_1(A_85, B_84, C_86)=A_85 | ~v1_funct_2(C_86, A_85, B_84) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_85, B_84))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.40/1.83  tff(c_438, plain, (k2_relat_1('#skF_5')=k1_xboole_0 | k1_relset_1(k2_struct_0('#skF_3'), k2_relat_1('#skF_5'), '#skF_5')=k2_struct_0('#skF_3') | ~v1_funct_2('#skF_5', k2_struct_0('#skF_3'), k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_297, c_435])).
% 4.40/1.83  tff(c_449, plain, (k2_relat_1('#skF_5')=k1_xboole_0 | k2_struct_0('#skF_3')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_298, c_357, c_438])).
% 4.40/1.83  tff(c_450, plain, (k2_struct_0('#skF_3')=k1_relat_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_295, c_449])).
% 4.40/1.83  tff(c_479, plain, (v1_funct_2('#skF_5', k1_relat_1('#skF_5'), k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_450, c_298])).
% 4.40/1.83  tff(c_292, plain, (k2_relset_1(k2_struct_0('#skF_3'), k2_relat_1('#skF_5'), '#skF_5')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_287, c_286])).
% 4.40/1.83  tff(c_477, plain, (k2_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_450, c_292])).
% 4.40/1.83  tff(c_476, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_450, c_297])).
% 4.40/1.83  tff(c_661, plain, (![A_105, B_106, C_107]: (k2_tops_2(A_105, B_106, C_107)=k2_funct_1(C_107) | ~v2_funct_1(C_107) | k2_relset_1(A_105, B_106, C_107)!=B_106 | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))) | ~v1_funct_2(C_107, A_105, B_106) | ~v1_funct_1(C_107))), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.40/1.83  tff(c_667, plain, (k2_tops_2(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5')=k2_funct_1('#skF_5') | ~v2_funct_1('#skF_5') | k2_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5')!=k2_relat_1('#skF_5') | ~v1_funct_2('#skF_5', k1_relat_1('#skF_5'), k2_relat_1('#skF_5')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_476, c_661])).
% 4.40/1.83  tff(c_679, plain, (k2_tops_2(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5')=k2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_479, c_477, c_64, c_667])).
% 4.40/1.83  tff(c_62, plain, (k2_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'))!=k2_struct_0('#skF_3') | k1_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'))!=k2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_172])).
% 4.40/1.83  tff(c_180, plain, (k2_relset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_3'), k2_tops_2(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'), '#skF_5'))!=k2_struct_0('#skF_3') | k1_relset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_3'), k2_tops_2(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'), '#skF_5'))!=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_120, c_119, c_119, c_120, c_120, c_119, c_119, c_62])).
% 4.40/1.83  tff(c_181, plain, (k1_relset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_3'), k2_tops_2(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'), '#skF_5'))!=k2_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_180])).
% 4.40/1.83  tff(c_294, plain, (k1_relset_1(k2_relat_1('#skF_5'), k2_struct_0('#skF_3'), k2_tops_2(k2_struct_0('#skF_3'), k2_relat_1('#skF_5'), '#skF_5'))!=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_287, c_287, c_287, c_181])).
% 4.40/1.83  tff(c_474, plain, (k1_relset_1(k2_relat_1('#skF_5'), k1_relat_1('#skF_5'), k2_tops_2(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5'))!=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_450, c_450, c_294])).
% 4.40/1.83  tff(c_685, plain, (k1_relset_1(k2_relat_1('#skF_5'), k1_relat_1('#skF_5'), k2_funct_1('#skF_5'))!=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_679, c_474])).
% 4.40/1.83  tff(c_546, plain, (![A_90, B_91, C_92]: (v1_funct_2(k2_tops_2(A_90, B_91, C_92), B_91, A_90) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))) | ~v1_funct_2(C_92, A_90, B_91) | ~v1_funct_1(C_92))), inference(cnfTransformation, [status(thm)], [f_148])).
% 4.40/1.83  tff(c_548, plain, (v1_funct_2(k2_tops_2(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5'), k2_relat_1('#skF_5'), k1_relat_1('#skF_5')) | ~v1_funct_2('#skF_5', k1_relat_1('#skF_5'), k2_relat_1('#skF_5')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_476, c_546])).
% 4.40/1.83  tff(c_557, plain, (v1_funct_2(k2_tops_2(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5'), k2_relat_1('#skF_5'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_479, c_548])).
% 4.40/1.83  tff(c_686, plain, (v1_funct_2(k2_funct_1('#skF_5'), k2_relat_1('#skF_5'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_679, c_557])).
% 4.40/1.83  tff(c_691, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_5'), k1_relat_1('#skF_5')))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5')))) | ~v1_funct_2('#skF_5', k1_relat_1('#skF_5'), k2_relat_1('#skF_5')) | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_679, c_56])).
% 4.40/1.83  tff(c_695, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_5'), k1_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_479, c_476, c_691])).
% 4.40/1.83  tff(c_38, plain, (![B_18, A_17, C_19]: (k1_xboole_0=B_18 | k1_relset_1(A_17, B_18, C_19)=A_17 | ~v1_funct_2(C_19, A_17, B_18) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.40/1.83  tff(c_731, plain, (k1_relat_1('#skF_5')=k1_xboole_0 | k1_relset_1(k2_relat_1('#skF_5'), k1_relat_1('#skF_5'), k2_funct_1('#skF_5'))=k2_relat_1('#skF_5') | ~v1_funct_2(k2_funct_1('#skF_5'), k2_relat_1('#skF_5'), k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_695, c_38])).
% 4.40/1.83  tff(c_767, plain, (k1_relat_1('#skF_5')=k1_xboole_0 | k1_relset_1(k2_relat_1('#skF_5'), k1_relat_1('#skF_5'), k2_funct_1('#skF_5'))=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_686, c_731])).
% 4.40/1.83  tff(c_768, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_685, c_767])).
% 4.40/1.83  tff(c_781, plain, (v1_funct_2(k2_funct_1('#skF_5'), k2_relat_1('#skF_5'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_768, c_686])).
% 4.40/1.83  tff(c_779, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_5'), k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_768, c_695])).
% 4.40/1.83  tff(c_30, plain, (![C_19, A_17]: (k1_xboole_0=C_19 | ~v1_funct_2(C_19, A_17, k1_xboole_0) | k1_xboole_0=A_17 | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.40/1.83  tff(c_942, plain, (k2_funct_1('#skF_5')=k1_xboole_0 | ~v1_funct_2(k2_funct_1('#skF_5'), k2_relat_1('#skF_5'), k1_xboole_0) | k2_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_779, c_30])).
% 4.40/1.83  tff(c_985, plain, (k2_funct_1('#skF_5')=k1_xboole_0 | k2_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_781, c_942])).
% 4.40/1.83  tff(c_986, plain, (k2_funct_1('#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_295, c_985])).
% 4.40/1.83  tff(c_20, plain, (![A_7]: (k1_relat_1(k2_funct_1(A_7))=k2_relat_1(A_7) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.40/1.83  tff(c_1012, plain, (k2_relat_1('#skF_5')=k1_relat_1(k1_xboole_0) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_986, c_20])).
% 4.40/1.83  tff(c_1019, plain, (k2_relat_1('#skF_5')=k1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_160, c_72, c_64, c_1012])).
% 4.40/1.83  tff(c_780, plain, (k1_relset_1(k2_relat_1('#skF_5'), k1_xboole_0, k2_funct_1('#skF_5'))!=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_768, c_685])).
% 4.40/1.83  tff(c_1002, plain, (k1_relset_1(k2_relat_1('#skF_5'), k1_xboole_0, k1_xboole_0)!=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_986, c_780])).
% 4.40/1.83  tff(c_1106, plain, (k1_relset_1(k1_relat_1(k1_xboole_0), k1_xboole_0, k1_xboole_0)!=k1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1019, c_1019, c_1002])).
% 4.40/1.83  tff(c_787, plain, (v1_funct_2('#skF_5', k1_xboole_0, k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_768, c_479])).
% 4.40/1.83  tff(c_1037, plain, (v1_funct_2('#skF_5', k1_xboole_0, k1_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_1019, c_787])).
% 4.40/1.83  tff(c_782, plain, (k2_tops_2(k1_xboole_0, k2_relat_1('#skF_5'), '#skF_5')=k2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_768, c_679])).
% 4.40/1.83  tff(c_1005, plain, (k2_tops_2(k1_xboole_0, k2_relat_1('#skF_5'), '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_986, c_782])).
% 4.40/1.83  tff(c_1073, plain, (k2_tops_2(k1_xboole_0, k1_relat_1(k1_xboole_0), '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1019, c_1005])).
% 4.40/1.83  tff(c_786, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k2_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_768, c_476])).
% 4.40/1.83  tff(c_1038, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_relat_1(k1_xboole_0))))), inference(demodulation, [status(thm), theory('equality')], [c_1019, c_786])).
% 4.40/1.83  tff(c_584, plain, (![A_98, B_99, C_100]: (m1_subset_1(k2_tops_2(A_98, B_99, C_100), k1_zfmisc_1(k2_zfmisc_1(B_99, A_98))) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))) | ~v1_funct_2(C_100, A_98, B_99) | ~v1_funct_1(C_100))), inference(cnfTransformation, [status(thm)], [f_148])).
% 4.40/1.83  tff(c_630, plain, (![B_99, A_98, C_100]: (k1_relset_1(B_99, A_98, k2_tops_2(A_98, B_99, C_100))=k1_relat_1(k2_tops_2(A_98, B_99, C_100)) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))) | ~v1_funct_2(C_100, A_98, B_99) | ~v1_funct_1(C_100))), inference(resolution, [status(thm)], [c_584, c_24])).
% 4.40/1.83  tff(c_1108, plain, (k1_relset_1(k1_relat_1(k1_xboole_0), k1_xboole_0, k2_tops_2(k1_xboole_0, k1_relat_1(k1_xboole_0), '#skF_5'))=k1_relat_1(k2_tops_2(k1_xboole_0, k1_relat_1(k1_xboole_0), '#skF_5')) | ~v1_funct_2('#skF_5', k1_xboole_0, k1_relat_1(k1_xboole_0)) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_1038, c_630])).
% 4.40/1.83  tff(c_1151, plain, (k1_relset_1(k1_relat_1(k1_xboole_0), k1_xboole_0, k1_xboole_0)=k1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1037, c_1073, c_1073, c_1108])).
% 4.40/1.83  tff(c_1153, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1106, c_1151])).
% 4.40/1.83  tff(c_1154, plain, ('#skF_1'('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_242])).
% 4.40/1.83  tff(c_44, plain, (![A_21]: (~v1_xboole_0('#skF_1'(A_21)) | ~l1_struct_0(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.40/1.83  tff(c_1166, plain, (~v1_xboole_0(k1_xboole_0) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1154, c_44])).
% 4.40/1.83  tff(c_1176, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_79, c_1166])).
% 4.40/1.83  tff(c_1178, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_1176])).
% 4.40/1.83  tff(c_1179, plain, (k2_relset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_3'), k2_tops_2(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'), '#skF_5'))!=k2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_180])).
% 4.40/1.83  tff(c_1375, plain, (k2_relset_1(k2_relat_1('#skF_5'), k2_struct_0('#skF_3'), k2_tops_2(k2_struct_0('#skF_3'), k2_relat_1('#skF_5'), '#skF_5'))!=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1297, c_1297, c_1179])).
% 4.40/1.83  tff(c_1465, plain, (k2_relset_1(k2_relat_1('#skF_5'), k1_relat_1('#skF_5'), k2_tops_2(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5'))!=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1458, c_1458, c_1458, c_1375])).
% 4.40/1.83  tff(c_1691, plain, (k2_relset_1(k2_relat_1('#skF_5'), k1_relat_1('#skF_5'), k2_funct_1('#skF_5'))!=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1683, c_1465])).
% 4.40/1.83  tff(c_1805, plain, (k2_relat_1(k2_funct_1('#skF_5'))!=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1798, c_1691])).
% 4.40/1.83  tff(c_1812, plain, (~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_18, c_1805])).
% 4.40/1.83  tff(c_1816, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_160, c_72, c_64, c_1812])).
% 4.40/1.83  tff(c_1817, plain, ('#skF_1'('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1241])).
% 4.40/1.83  tff(c_1829, plain, (~v1_xboole_0(k1_xboole_0) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1817, c_44])).
% 4.40/1.83  tff(c_1839, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_79, c_1829])).
% 4.40/1.83  tff(c_1841, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_1839])).
% 4.40/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.40/1.83  
% 4.40/1.83  Inference rules
% 4.40/1.83  ----------------------
% 4.40/1.83  #Ref     : 0
% 4.40/1.83  #Sup     : 372
% 4.40/1.83  #Fact    : 0
% 4.40/1.83  #Define  : 0
% 4.40/1.83  #Split   : 7
% 4.40/1.83  #Chain   : 0
% 4.40/1.83  #Close   : 0
% 4.40/1.83  
% 4.40/1.83  Ordering : KBO
% 4.40/1.83  
% 4.40/1.83  Simplification rules
% 4.40/1.83  ----------------------
% 4.40/1.83  #Subsume      : 64
% 4.40/1.83  #Demod        : 353
% 4.40/1.83  #Tautology    : 161
% 4.40/1.83  #SimpNegUnit  : 73
% 4.40/1.83  #BackRed      : 75
% 4.40/1.83  
% 4.40/1.83  #Partial instantiations: 0
% 4.40/1.83  #Strategies tried      : 1
% 4.40/1.83  
% 4.40/1.83  Timing (in seconds)
% 4.40/1.83  ----------------------
% 4.40/1.84  Preprocessing        : 0.38
% 4.40/1.84  Parsing              : 0.21
% 4.40/1.84  CNF conversion       : 0.02
% 4.40/1.84  Main loop            : 0.57
% 4.40/1.84  Inferencing          : 0.19
% 4.40/1.84  Reduction            : 0.20
% 4.40/1.84  Demodulation         : 0.14
% 4.40/1.84  BG Simplification    : 0.03
% 4.40/1.84  Subsumption          : 0.09
% 4.40/1.84  Abstraction          : 0.03
% 4.40/1.84  MUC search           : 0.00
% 4.40/1.84  Cooper               : 0.00
% 4.40/1.84  Total                : 1.03
% 4.40/1.84  Index Insertion      : 0.00
% 4.40/1.84  Index Deletion       : 0.00
% 4.40/1.84  Index Matching       : 0.00
% 4.40/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
