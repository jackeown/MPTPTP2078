%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1005+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:14 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 2.95s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 170 expanded)
%              Number of leaves         :   37 (  74 expanded)
%              Depth                    :   16
%              Number of atoms          :   88 ( 271 expanded)
%              Number of equality atoms :   17 (  52 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_5 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_53,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_50,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k7_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_2)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_45,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(E,k1_relat_1(A))
                  & r2_hidden(E,B)
                  & D = k1_funct_1(A,E) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_32,plain,(
    ! [A_49] : m1_subset_1('#skF_5'(A_49),A_49) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_38,plain,(
    ! [A_58,B_59] :
      ( r2_hidden(A_58,B_59)
      | v1_xboole_0(B_59)
      | ~ m1_subset_1(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_30,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_52,plain,(
    ! [A_65] :
      ( k1_xboole_0 = A_65
      | ~ v1_xboole_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_56,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_52])).

tff(c_57,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_30])).

tff(c_46,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_88,plain,(
    ! [A_76,B_77,C_78] :
      ( k1_relset_1(A_76,B_77,C_78) = k1_relat_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_96,plain,(
    k1_relset_1(k1_xboole_0,'#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_46,c_88])).

tff(c_108,plain,(
    ! [A_81,B_82,C_83] :
      ( m1_subset_1(k1_relset_1(A_81,B_82,C_83),k1_zfmisc_1(A_81))
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_121,plain,
    ( m1_subset_1(k1_relat_1('#skF_8'),k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_108])).

tff(c_126,plain,(
    m1_subset_1(k1_relat_1('#skF_8'),k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_121])).

tff(c_40,plain,(
    ! [C_62,B_61,A_60] :
      ( ~ v1_xboole_0(C_62)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(C_62))
      | ~ r2_hidden(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_128,plain,(
    ! [A_60] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_60,k1_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_126,c_40])).

tff(c_132,plain,(
    ! [A_84] : ~ r2_hidden(A_84,k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_128])).

tff(c_137,plain,(
    ! [A_58] :
      ( v1_xboole_0(k1_relat_1('#skF_8'))
      | ~ m1_subset_1(A_58,k1_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_38,c_132])).

tff(c_139,plain,(
    ! [A_85] : ~ m1_subset_1(A_85,k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_137])).

tff(c_144,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_32,c_139])).

tff(c_145,plain,(
    v1_xboole_0(k1_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_137])).

tff(c_42,plain,(
    ! [A_63] :
      ( k1_xboole_0 = A_63
      | ~ v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_149,plain,(
    k1_relat_1('#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_145,c_42])).

tff(c_131,plain,(
    ! [A_60] : ~ r2_hidden(A_60,k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_128])).

tff(c_163,plain,(
    ! [A_60] : ~ r2_hidden(A_60,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_131])).

tff(c_67,plain,(
    ! [C_66,A_67,B_68] :
      ( v1_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_75,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_46,c_67])).

tff(c_50,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_628,plain,(
    ! [A_165,B_166,D_167] :
      ( r2_hidden('#skF_4'(A_165,B_166,k9_relat_1(A_165,B_166),D_167),k1_relat_1(A_165))
      | ~ r2_hidden(D_167,k9_relat_1(A_165,B_166))
      | ~ v1_funct_1(A_165)
      | ~ v1_relat_1(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_644,plain,(
    ! [B_166,D_167] :
      ( r2_hidden('#skF_4'('#skF_8',B_166,k9_relat_1('#skF_8',B_166),D_167),k1_xboole_0)
      | ~ r2_hidden(D_167,k9_relat_1('#skF_8',B_166))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_628])).

tff(c_655,plain,(
    ! [B_166,D_167] :
      ( r2_hidden('#skF_4'('#skF_8',B_166,k9_relat_1('#skF_8',B_166),D_167),k1_xboole_0)
      | ~ r2_hidden(D_167,k9_relat_1('#skF_8',B_166)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_50,c_644])).

tff(c_657,plain,(
    ! [D_168,B_169] : ~ r2_hidden(D_168,k9_relat_1('#skF_8',B_169)) ),
    inference(negUnitSimplification,[status(thm)],[c_163,c_655])).

tff(c_683,plain,(
    ! [B_170,A_171] :
      ( v1_xboole_0(k9_relat_1('#skF_8',B_170))
      | ~ m1_subset_1(A_171,k9_relat_1('#skF_8',B_170)) ) ),
    inference(resolution,[status(thm)],[c_38,c_657])).

tff(c_699,plain,(
    ! [B_172] : v1_xboole_0(k9_relat_1('#skF_8',B_172)) ),
    inference(resolution,[status(thm)],[c_32,c_683])).

tff(c_709,plain,(
    ! [B_172] : k9_relat_1('#skF_8',B_172) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_699,c_42])).

tff(c_150,plain,(
    ! [A_86,B_87,C_88,D_89] :
      ( k7_relset_1(A_86,B_87,C_88,D_89) = k9_relat_1(C_88,D_89)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_160,plain,(
    ! [D_89] : k7_relset_1(k1_xboole_0,'#skF_6','#skF_8',D_89) = k9_relat_1('#skF_8',D_89) ),
    inference(resolution,[status(thm)],[c_46,c_150])).

tff(c_44,plain,(
    k7_relset_1(k1_xboole_0,'#skF_6','#skF_8','#skF_7') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_183,plain,(
    k9_relat_1('#skF_8','#skF_7') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_44])).

tff(c_747,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_709,c_183])).

%------------------------------------------------------------------------------
