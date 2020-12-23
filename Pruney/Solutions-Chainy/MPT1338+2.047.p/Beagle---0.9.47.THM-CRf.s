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
% DateTime   : Thu Dec  3 10:23:20 EST 2020

% Result     : Theorem 2.83s
% Output     : CNFRefutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 414 expanded)
%              Number of leaves         :   35 ( 168 expanded)
%              Depth                    :    9
%              Number of atoms          :  135 (1296 expanded)
%              Number of equality atoms :   60 ( 472 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k3_relset_1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k4_relat_1 > k2_struct_0 > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relset_1,type,(
    k3_relset_1: ( $i * $i * $i ) > $i )).

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_114,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_66,axiom,(
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

tff(f_38,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_34,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k3_relset_1(A,B,C) = k4_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_relset_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k1_relset_1(B,A,k3_relset_1(A,B,C)) = k2_relset_1(A,B,C)
        & k2_relset_1(B,A,k3_relset_1(A,B,C)) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_relset_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_78,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_44,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_48,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_49,plain,(
    ! [A_23] :
      ( u1_struct_0(A_23) = k2_struct_0(A_23)
      | ~ l1_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_57,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_49])).

tff(c_56,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_49])).

tff(c_40,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_66,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_56,c_40])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_68,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_56,c_38])).

tff(c_186,plain,(
    ! [B_69,A_70,C_71] :
      ( k1_xboole_0 = B_69
      | k1_relset_1(A_70,B_69,C_71) = A_70
      | ~ v1_funct_2(C_71,A_70,B_69)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_70,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_189,plain,
    ( k2_struct_0('#skF_2') = k1_xboole_0
    | k1_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_1')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_68,c_186])).

tff(c_192,plain,
    ( k2_struct_0('#skF_2') = k1_xboole_0
    | k1_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_189])).

tff(c_197,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_192])).

tff(c_69,plain,(
    ! [C_25,A_26,B_27] :
      ( v1_relat_1(C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_73,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_69])).

tff(c_42,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_34,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_79,plain,(
    ! [A_28] :
      ( k4_relat_1(A_28) = k2_funct_1(A_28)
      | ~ v2_funct_1(A_28)
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_82,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_79])).

tff(c_85,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_42,c_82])).

tff(c_91,plain,(
    ! [A_30,B_31,C_32] :
      ( k3_relset_1(A_30,B_31,C_32) = k4_relat_1(C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_94,plain,(
    k3_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k4_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_91])).

tff(c_96,plain,(
    k3_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_94])).

tff(c_166,plain,(
    ! [B_60,A_61,C_62] :
      ( k2_relset_1(B_60,A_61,k3_relset_1(A_61,B_60,C_62)) = k1_relset_1(A_61,B_60,C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_61,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_168,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k3_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) = k1_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_166])).

tff(c_170,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k1_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_168])).

tff(c_198,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_170])).

tff(c_36,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_74,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_56,c_36])).

tff(c_207,plain,(
    ! [A_72,B_73,C_74] :
      ( k2_tops_2(A_72,B_73,C_74) = k2_funct_1(C_74)
      | ~ v2_funct_1(C_74)
      | k2_relset_1(A_72,B_73,C_74) != B_73
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73)))
      | ~ v1_funct_2(C_74,A_72,B_73)
      | ~ v1_funct_1(C_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_210,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_207])).

tff(c_213,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_66,c_74,c_34,c_210])).

tff(c_133,plain,(
    ! [B_48,A_49,C_50] :
      ( k1_relset_1(B_48,A_49,k3_relset_1(A_49,B_48,C_50)) = k2_relset_1(A_49,B_48,C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_49,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_135,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k3_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) = k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_133])).

tff(c_137,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_74,c_135])).

tff(c_142,plain,(
    ! [A_51,B_52,C_53] :
      ( k2_tops_2(A_51,B_52,C_53) = k2_funct_1(C_53)
      | ~ v2_funct_1(C_53)
      | k2_relset_1(A_51,B_52,C_53) != B_52
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52)))
      | ~ v1_funct_2(C_53,A_51,B_52)
      | ~ v1_funct_1(C_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_145,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_142])).

tff(c_148,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_66,c_74,c_34,c_145])).

tff(c_32,plain,
    ( k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_97,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_57,c_56,c_56,c_57,c_57,c_56,c_56,c_32])).

tff(c_98,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_97])).

tff(c_149,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_98])).

tff(c_152,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_149])).

tff(c_153,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_97])).

tff(c_215,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_153])).

tff(c_219,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_215])).

tff(c_220,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_192])).

tff(c_28,plain,(
    ! [A_15] :
      ( ~ v1_xboole_0(k2_struct_0(A_15))
      | ~ l1_struct_0(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_234,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_28])).

tff(c_238,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2,c_234])).

tff(c_240,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_238])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:19:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.83/1.75  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.76  
% 2.83/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.77  %$ v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k3_relset_1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k4_relat_1 > k2_struct_0 > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.83/1.77  
% 2.83/1.77  %Foreground sorts:
% 2.83/1.77  
% 2.83/1.77  
% 2.83/1.77  %Background operators:
% 2.83/1.77  
% 2.83/1.77  
% 2.83/1.77  %Foreground operators:
% 2.83/1.77  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.83/1.77  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.83/1.77  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.83/1.77  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.83/1.77  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.83/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.83/1.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.83/1.77  tff(k3_relset_1, type, k3_relset_1: ($i * $i * $i) > $i).
% 2.83/1.77  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 2.83/1.77  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.83/1.77  tff('#skF_2', type, '#skF_2': $i).
% 2.83/1.77  tff('#skF_3', type, '#skF_3': $i).
% 2.83/1.77  tff('#skF_1', type, '#skF_1': $i).
% 2.83/1.77  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.83/1.77  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.83/1.77  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.83/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.83/1.77  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.83/1.77  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.83/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.83/1.77  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.83/1.77  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.83/1.77  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.83/1.77  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.83/1.77  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.83/1.77  
% 3.17/1.79  tff(f_114, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_2)).
% 3.17/1.79  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.17/1.79  tff(f_70, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.17/1.79  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.17/1.79  tff(f_38, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.17/1.79  tff(f_34, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 3.17/1.79  tff(f_42, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k3_relset_1(A, B, C) = k4_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_relset_1)).
% 3.17/1.79  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k1_relset_1(B, A, k3_relset_1(A, B, C)) = k2_relset_1(A, B, C)) & (k2_relset_1(B, A, k3_relset_1(A, B, C)) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_relset_1)).
% 3.17/1.79  tff(f_90, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 3.17/1.79  tff(f_78, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_struct_0)).
% 3.17/1.79  tff(c_46, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.17/1.79  tff(c_44, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.17/1.79  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.17/1.79  tff(c_48, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.17/1.79  tff(c_49, plain, (![A_23]: (u1_struct_0(A_23)=k2_struct_0(A_23) | ~l1_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.17/1.79  tff(c_57, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_48, c_49])).
% 3.17/1.79  tff(c_56, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_49])).
% 3.17/1.79  tff(c_40, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.17/1.79  tff(c_66, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_56, c_40])).
% 3.17/1.79  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.17/1.79  tff(c_68, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_56, c_38])).
% 3.17/1.79  tff(c_186, plain, (![B_69, A_70, C_71]: (k1_xboole_0=B_69 | k1_relset_1(A_70, B_69, C_71)=A_70 | ~v1_funct_2(C_71, A_70, B_69) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_70, B_69))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.17/1.79  tff(c_189, plain, (k2_struct_0('#skF_2')=k1_xboole_0 | k1_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_1') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_68, c_186])).
% 3.17/1.79  tff(c_192, plain, (k2_struct_0('#skF_2')=k1_xboole_0 | k1_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_189])).
% 3.17/1.79  tff(c_197, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_192])).
% 3.17/1.79  tff(c_69, plain, (![C_25, A_26, B_27]: (v1_relat_1(C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.17/1.79  tff(c_73, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_69])).
% 3.17/1.79  tff(c_42, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.17/1.79  tff(c_34, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.17/1.79  tff(c_79, plain, (![A_28]: (k4_relat_1(A_28)=k2_funct_1(A_28) | ~v2_funct_1(A_28) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.17/1.79  tff(c_82, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_79])).
% 3.17/1.79  tff(c_85, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_42, c_82])).
% 3.17/1.79  tff(c_91, plain, (![A_30, B_31, C_32]: (k3_relset_1(A_30, B_31, C_32)=k4_relat_1(C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.17/1.79  tff(c_94, plain, (k3_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k4_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_91])).
% 3.17/1.79  tff(c_96, plain, (k3_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_94])).
% 3.17/1.79  tff(c_166, plain, (![B_60, A_61, C_62]: (k2_relset_1(B_60, A_61, k3_relset_1(A_61, B_60, C_62))=k1_relset_1(A_61, B_60, C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_61, B_60))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.17/1.79  tff(c_168, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k3_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))=k1_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_68, c_166])).
% 3.17/1.79  tff(c_170, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k1_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_168])).
% 3.17/1.79  tff(c_198, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_197, c_170])).
% 3.17/1.79  tff(c_36, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.17/1.79  tff(c_74, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_57, c_56, c_36])).
% 3.17/1.79  tff(c_207, plain, (![A_72, B_73, C_74]: (k2_tops_2(A_72, B_73, C_74)=k2_funct_1(C_74) | ~v2_funct_1(C_74) | k2_relset_1(A_72, B_73, C_74)!=B_73 | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))) | ~v1_funct_2(C_74, A_72, B_73) | ~v1_funct_1(C_74))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.17/1.79  tff(c_210, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_207])).
% 3.17/1.79  tff(c_213, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_66, c_74, c_34, c_210])).
% 3.17/1.79  tff(c_133, plain, (![B_48, A_49, C_50]: (k1_relset_1(B_48, A_49, k3_relset_1(A_49, B_48, C_50))=k2_relset_1(A_49, B_48, C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_49, B_48))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.17/1.79  tff(c_135, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k3_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))=k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_68, c_133])).
% 3.17/1.79  tff(c_137, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_74, c_135])).
% 3.17/1.79  tff(c_142, plain, (![A_51, B_52, C_53]: (k2_tops_2(A_51, B_52, C_53)=k2_funct_1(C_53) | ~v2_funct_1(C_53) | k2_relset_1(A_51, B_52, C_53)!=B_52 | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))) | ~v1_funct_2(C_53, A_51, B_52) | ~v1_funct_1(C_53))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.17/1.79  tff(c_145, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_142])).
% 3.17/1.79  tff(c_148, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_66, c_74, c_34, c_145])).
% 3.17/1.79  tff(c_32, plain, (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.17/1.79  tff(c_97, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_57, c_57, c_56, c_56, c_57, c_57, c_56, c_56, c_32])).
% 3.17/1.79  tff(c_98, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_97])).
% 3.17/1.79  tff(c_149, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_148, c_98])).
% 3.17/1.79  tff(c_152, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_137, c_149])).
% 3.17/1.79  tff(c_153, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_97])).
% 3.17/1.79  tff(c_215, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_213, c_153])).
% 3.17/1.79  tff(c_219, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_198, c_215])).
% 3.17/1.79  tff(c_220, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_192])).
% 3.17/1.79  tff(c_28, plain, (![A_15]: (~v1_xboole_0(k2_struct_0(A_15)) | ~l1_struct_0(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.17/1.79  tff(c_234, plain, (~v1_xboole_0(k1_xboole_0) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_220, c_28])).
% 3.17/1.79  tff(c_238, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_2, c_234])).
% 3.17/1.79  tff(c_240, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_238])).
% 3.17/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.79  
% 3.17/1.79  Inference rules
% 3.17/1.79  ----------------------
% 3.17/1.79  #Ref     : 0
% 3.17/1.79  #Sup     : 46
% 3.17/1.79  #Fact    : 0
% 3.17/1.80  #Define  : 0
% 3.17/1.80  #Split   : 3
% 3.17/1.80  #Chain   : 0
% 3.17/1.80  #Close   : 0
% 3.17/1.80  
% 3.17/1.80  Ordering : KBO
% 3.17/1.80  
% 3.17/1.80  Simplification rules
% 3.17/1.80  ----------------------
% 3.17/1.80  #Subsume      : 0
% 3.17/1.80  #Demod        : 60
% 3.17/1.80  #Tautology    : 32
% 3.17/1.80  #SimpNegUnit  : 1
% 3.17/1.80  #BackRed      : 13
% 3.17/1.80  
% 3.17/1.80  #Partial instantiations: 0
% 3.17/1.80  #Strategies tried      : 1
% 3.17/1.80  
% 3.17/1.80  Timing (in seconds)
% 3.17/1.80  ----------------------
% 3.17/1.80  Preprocessing        : 0.54
% 3.17/1.80  Parsing              : 0.28
% 3.17/1.80  CNF conversion       : 0.03
% 3.17/1.80  Main loop            : 0.35
% 3.17/1.80  Inferencing          : 0.11
% 3.17/1.80  Reduction            : 0.12
% 3.17/1.80  Demodulation         : 0.09
% 3.17/1.80  BG Simplification    : 0.02
% 3.17/1.80  Subsumption          : 0.05
% 3.17/1.80  Abstraction          : 0.02
% 3.17/1.80  MUC search           : 0.00
% 3.17/1.80  Cooper               : 0.00
% 3.17/1.80  Total                : 0.95
% 3.17/1.80  Index Insertion      : 0.00
% 3.17/1.80  Index Deletion       : 0.00
% 3.17/1.80  Index Matching       : 0.00
% 3.17/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
