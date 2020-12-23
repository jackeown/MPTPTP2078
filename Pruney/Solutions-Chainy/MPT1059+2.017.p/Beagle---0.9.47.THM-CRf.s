%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:35 EST 2020

% Result     : Theorem 2.82s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 135 expanded)
%              Number of leaves         :   37 (  62 expanded)
%              Depth                    :   12
%              Number of atoms          :  135 ( 323 expanded)
%              Number of equality atoms :   34 (  66 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k7_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_partfun1,type,(
    k7_partfun1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_127,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,A,B)
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
               => ! [D] :
                    ( m1_subset_1(D,A)
                   => k7_partfun1(B,C,D) = k3_funct_2(A,B,C,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_2)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_83,axiom,(
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

tff(f_94,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_107,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_30,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_32,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_27,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_40,plain,(
    m1_subset_1('#skF_6','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_90,plain,(
    ! [C_59,B_60,A_61] :
      ( v5_relat_1(C_59,B_60)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_61,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_102,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_90])).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( r2_hidden(A_4,B_5)
      | v1_xboole_0(B_5)
      | ~ m1_subset_1(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_56,plain,(
    ! [C_46,A_47,B_48] :
      ( v1_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_68,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_56])).

tff(c_46,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_44,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_152,plain,(
    ! [A_75,B_76,C_77] :
      ( k1_relset_1(A_75,B_76,C_77) = k1_relat_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_164,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_152])).

tff(c_314,plain,(
    ! [B_102,A_103,C_104] :
      ( k1_xboole_0 = B_102
      | k1_relset_1(A_103,B_102,C_104) = A_103
      | ~ v1_funct_2(C_104,A_103,B_102)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_103,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_321,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_314])).

tff(c_333,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_164,c_321])).

tff(c_338,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_333])).

tff(c_403,plain,(
    ! [A_117,B_118,C_119] :
      ( k7_partfun1(A_117,B_118,C_119) = k1_funct_1(B_118,C_119)
      | ~ r2_hidden(C_119,k1_relat_1(B_118))
      | ~ v1_funct_1(B_118)
      | ~ v5_relat_1(B_118,A_117)
      | ~ v1_relat_1(B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_405,plain,(
    ! [A_117,C_119] :
      ( k7_partfun1(A_117,'#skF_5',C_119) = k1_funct_1('#skF_5',C_119)
      | ~ r2_hidden(C_119,'#skF_3')
      | ~ v1_funct_1('#skF_5')
      | ~ v5_relat_1('#skF_5',A_117)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_403])).

tff(c_412,plain,(
    ! [A_120,C_121] :
      ( k7_partfun1(A_120,'#skF_5',C_121) = k1_funct_1('#skF_5',C_121)
      | ~ r2_hidden(C_121,'#skF_3')
      | ~ v5_relat_1('#skF_5',A_120) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_46,c_405])).

tff(c_415,plain,(
    ! [A_120,A_4] :
      ( k7_partfun1(A_120,'#skF_5',A_4) = k1_funct_1('#skF_5',A_4)
      | ~ v5_relat_1('#skF_5',A_120)
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_4,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_8,c_412])).

tff(c_419,plain,(
    ! [A_122,A_123] :
      ( k7_partfun1(A_122,'#skF_5',A_123) = k1_funct_1('#skF_5',A_123)
      | ~ v5_relat_1('#skF_5',A_122)
      | ~ m1_subset_1(A_123,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_415])).

tff(c_423,plain,(
    ! [A_124] :
      ( k7_partfun1('#skF_4','#skF_5',A_124) = k1_funct_1('#skF_5',A_124)
      | ~ m1_subset_1(A_124,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_102,c_419])).

tff(c_437,plain,(
    k7_partfun1('#skF_4','#skF_5','#skF_6') = k1_funct_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_423])).

tff(c_38,plain,(
    k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_6') != k7_partfun1('#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_438,plain,(
    k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_6') != k1_funct_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_437,c_38])).

tff(c_461,plain,(
    ! [A_131,B_132,C_133,D_134] :
      ( k3_funct_2(A_131,B_132,C_133,D_134) = k1_funct_1(C_133,D_134)
      | ~ m1_subset_1(D_134,A_131)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132)))
      | ~ v1_funct_2(C_133,A_131,B_132)
      | ~ v1_funct_1(C_133)
      | v1_xboole_0(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_473,plain,(
    ! [B_132,C_133] :
      ( k3_funct_2('#skF_3',B_132,C_133,'#skF_6') = k1_funct_1(C_133,'#skF_6')
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_132)))
      | ~ v1_funct_2(C_133,'#skF_3',B_132)
      | ~ v1_funct_1(C_133)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_40,c_461])).

tff(c_494,plain,(
    ! [B_137,C_138] :
      ( k3_funct_2('#skF_3',B_137,C_138,'#skF_6') = k1_funct_1(C_138,'#skF_6')
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_137)))
      | ~ v1_funct_2(C_138,'#skF_3',B_137)
      | ~ v1_funct_1(C_138) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_473])).

tff(c_501,plain,
    ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_6') = k1_funct_1('#skF_5','#skF_6')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_494])).

tff(c_513,plain,(
    k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_6') = k1_funct_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_501])).

tff(c_515,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_438,c_513])).

tff(c_516,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_333])).

tff(c_4,plain,(
    ! [A_1] : m1_subset_1('#skF_2'(A_1),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_6,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_107,plain,(
    ! [C_65,B_66,A_67] :
      ( ~ v1_xboole_0(C_65)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(C_65))
      | ~ r2_hidden(A_67,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_116,plain,(
    ! [A_3,A_67] :
      ( ~ v1_xboole_0(A_3)
      | ~ r2_hidden(A_67,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_6,c_107])).

tff(c_130,plain,(
    ! [A_71] : ~ r2_hidden(A_71,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_116])).

tff(c_135,plain,(
    ! [A_4] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1(A_4,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_130])).

tff(c_138,plain,(
    ! [A_72] : ~ m1_subset_1(A_72,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_143,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_4,c_138])).

tff(c_144,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_527,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_516,c_144])).

tff(c_535,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_527])).

tff(c_536,plain,(
    ! [A_3] : ~ v1_xboole_0(A_3) ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_2,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_539,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_536,c_2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:43:29 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.82/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.39  
% 2.82/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.40  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k7_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_4
% 2.82/1.40  
% 2.82/1.40  %Foreground sorts:
% 2.82/1.40  
% 2.82/1.40  
% 2.82/1.40  %Background operators:
% 2.82/1.40  
% 2.82/1.40  
% 2.82/1.40  %Foreground operators:
% 2.82/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.82/1.40  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.82/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.82/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.82/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.82/1.40  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 2.82/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.82/1.40  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.82/1.40  tff('#skF_6', type, '#skF_6': $i).
% 2.82/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.82/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.82/1.40  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.82/1.40  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.82/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.82/1.40  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.82/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.82/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.82/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.82/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.82/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.82/1.40  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.82/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.82/1.40  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.82/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.82/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.82/1.40  
% 2.82/1.41  tff(f_127, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, A) => (k7_partfun1(B, C, D) = k3_funct_2(A, B, C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t176_funct_2)).
% 2.82/1.41  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.82/1.41  tff(f_38, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.82/1.41  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.82/1.41  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.82/1.41  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.82/1.41  tff(f_94, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_partfun1)).
% 2.82/1.41  tff(f_107, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.82/1.41  tff(f_30, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 2.82/1.41  tff(f_32, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.82/1.41  tff(f_51, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.82/1.41  tff(f_27, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_xboole_0)).
% 2.82/1.41  tff(c_48, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.82/1.41  tff(c_40, plain, (m1_subset_1('#skF_6', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.82/1.41  tff(c_42, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.82/1.41  tff(c_90, plain, (![C_59, B_60, A_61]: (v5_relat_1(C_59, B_60) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_61, B_60))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.82/1.41  tff(c_102, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_90])).
% 2.82/1.41  tff(c_50, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.82/1.41  tff(c_8, plain, (![A_4, B_5]: (r2_hidden(A_4, B_5) | v1_xboole_0(B_5) | ~m1_subset_1(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.82/1.41  tff(c_56, plain, (![C_46, A_47, B_48]: (v1_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.82/1.41  tff(c_68, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_42, c_56])).
% 2.82/1.41  tff(c_46, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.82/1.41  tff(c_44, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.82/1.41  tff(c_152, plain, (![A_75, B_76, C_77]: (k1_relset_1(A_75, B_76, C_77)=k1_relat_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.82/1.41  tff(c_164, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_42, c_152])).
% 2.82/1.41  tff(c_314, plain, (![B_102, A_103, C_104]: (k1_xboole_0=B_102 | k1_relset_1(A_103, B_102, C_104)=A_103 | ~v1_funct_2(C_104, A_103, B_102) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_103, B_102))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.82/1.41  tff(c_321, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_314])).
% 2.82/1.41  tff(c_333, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_164, c_321])).
% 2.82/1.41  tff(c_338, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_333])).
% 2.82/1.41  tff(c_403, plain, (![A_117, B_118, C_119]: (k7_partfun1(A_117, B_118, C_119)=k1_funct_1(B_118, C_119) | ~r2_hidden(C_119, k1_relat_1(B_118)) | ~v1_funct_1(B_118) | ~v5_relat_1(B_118, A_117) | ~v1_relat_1(B_118))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.82/1.41  tff(c_405, plain, (![A_117, C_119]: (k7_partfun1(A_117, '#skF_5', C_119)=k1_funct_1('#skF_5', C_119) | ~r2_hidden(C_119, '#skF_3') | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', A_117) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_338, c_403])).
% 2.82/1.41  tff(c_412, plain, (![A_120, C_121]: (k7_partfun1(A_120, '#skF_5', C_121)=k1_funct_1('#skF_5', C_121) | ~r2_hidden(C_121, '#skF_3') | ~v5_relat_1('#skF_5', A_120))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_46, c_405])).
% 2.82/1.41  tff(c_415, plain, (![A_120, A_4]: (k7_partfun1(A_120, '#skF_5', A_4)=k1_funct_1('#skF_5', A_4) | ~v5_relat_1('#skF_5', A_120) | v1_xboole_0('#skF_3') | ~m1_subset_1(A_4, '#skF_3'))), inference(resolution, [status(thm)], [c_8, c_412])).
% 2.82/1.41  tff(c_419, plain, (![A_122, A_123]: (k7_partfun1(A_122, '#skF_5', A_123)=k1_funct_1('#skF_5', A_123) | ~v5_relat_1('#skF_5', A_122) | ~m1_subset_1(A_123, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_50, c_415])).
% 2.82/1.41  tff(c_423, plain, (![A_124]: (k7_partfun1('#skF_4', '#skF_5', A_124)=k1_funct_1('#skF_5', A_124) | ~m1_subset_1(A_124, '#skF_3'))), inference(resolution, [status(thm)], [c_102, c_419])).
% 2.82/1.41  tff(c_437, plain, (k7_partfun1('#skF_4', '#skF_5', '#skF_6')=k1_funct_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_40, c_423])).
% 2.82/1.41  tff(c_38, plain, (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6')!=k7_partfun1('#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.82/1.41  tff(c_438, plain, (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6')!=k1_funct_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_437, c_38])).
% 2.82/1.41  tff(c_461, plain, (![A_131, B_132, C_133, D_134]: (k3_funct_2(A_131, B_132, C_133, D_134)=k1_funct_1(C_133, D_134) | ~m1_subset_1(D_134, A_131) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))) | ~v1_funct_2(C_133, A_131, B_132) | ~v1_funct_1(C_133) | v1_xboole_0(A_131))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.82/1.41  tff(c_473, plain, (![B_132, C_133]: (k3_funct_2('#skF_3', B_132, C_133, '#skF_6')=k1_funct_1(C_133, '#skF_6') | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_132))) | ~v1_funct_2(C_133, '#skF_3', B_132) | ~v1_funct_1(C_133) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_40, c_461])).
% 2.82/1.41  tff(c_494, plain, (![B_137, C_138]: (k3_funct_2('#skF_3', B_137, C_138, '#skF_6')=k1_funct_1(C_138, '#skF_6') | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_137))) | ~v1_funct_2(C_138, '#skF_3', B_137) | ~v1_funct_1(C_138))), inference(negUnitSimplification, [status(thm)], [c_50, c_473])).
% 2.82/1.41  tff(c_501, plain, (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6')=k1_funct_1('#skF_5', '#skF_6') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_42, c_494])).
% 2.82/1.41  tff(c_513, plain, (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6')=k1_funct_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_501])).
% 2.82/1.41  tff(c_515, plain, $false, inference(negUnitSimplification, [status(thm)], [c_438, c_513])).
% 2.82/1.41  tff(c_516, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_333])).
% 2.82/1.41  tff(c_4, plain, (![A_1]: (m1_subset_1('#skF_2'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.82/1.41  tff(c_6, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.82/1.41  tff(c_107, plain, (![C_65, B_66, A_67]: (~v1_xboole_0(C_65) | ~m1_subset_1(B_66, k1_zfmisc_1(C_65)) | ~r2_hidden(A_67, B_66))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.82/1.41  tff(c_116, plain, (![A_3, A_67]: (~v1_xboole_0(A_3) | ~r2_hidden(A_67, k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_107])).
% 2.82/1.41  tff(c_130, plain, (![A_71]: (~r2_hidden(A_71, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_116])).
% 2.82/1.41  tff(c_135, plain, (![A_4]: (v1_xboole_0(k1_xboole_0) | ~m1_subset_1(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_130])).
% 2.82/1.41  tff(c_138, plain, (![A_72]: (~m1_subset_1(A_72, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_135])).
% 2.82/1.41  tff(c_143, plain, $false, inference(resolution, [status(thm)], [c_4, c_138])).
% 2.82/1.41  tff(c_144, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_135])).
% 2.82/1.41  tff(c_527, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_516, c_144])).
% 2.82/1.41  tff(c_535, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_527])).
% 2.82/1.41  tff(c_536, plain, (![A_3]: (~v1_xboole_0(A_3))), inference(splitRight, [status(thm)], [c_116])).
% 2.82/1.41  tff(c_2, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.82/1.41  tff(c_539, plain, $false, inference(negUnitSimplification, [status(thm)], [c_536, c_2])).
% 2.82/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.41  
% 2.82/1.41  Inference rules
% 2.82/1.41  ----------------------
% 2.82/1.41  #Ref     : 0
% 2.82/1.41  #Sup     : 91
% 2.82/1.41  #Fact    : 0
% 2.82/1.41  #Define  : 0
% 2.82/1.41  #Split   : 7
% 2.82/1.41  #Chain   : 0
% 2.82/1.41  #Close   : 0
% 2.82/1.41  
% 2.82/1.41  Ordering : KBO
% 2.82/1.41  
% 2.82/1.41  Simplification rules
% 2.82/1.41  ----------------------
% 2.82/1.41  #Subsume      : 6
% 2.82/1.41  #Demod        : 55
% 2.82/1.41  #Tautology    : 25
% 2.82/1.41  #SimpNegUnit  : 8
% 2.82/1.41  #BackRed      : 20
% 2.82/1.41  
% 2.82/1.41  #Partial instantiations: 0
% 2.82/1.41  #Strategies tried      : 1
% 2.82/1.41  
% 2.82/1.41  Timing (in seconds)
% 2.82/1.41  ----------------------
% 2.82/1.42  Preprocessing        : 0.34
% 2.82/1.42  Parsing              : 0.18
% 2.82/1.42  CNF conversion       : 0.02
% 2.82/1.42  Main loop            : 0.31
% 2.82/1.42  Inferencing          : 0.11
% 2.82/1.42  Reduction            : 0.10
% 2.82/1.42  Demodulation         : 0.07
% 2.82/1.42  BG Simplification    : 0.02
% 2.82/1.42  Subsumption          : 0.05
% 2.82/1.42  Abstraction          : 0.01
% 2.82/1.42  MUC search           : 0.00
% 2.82/1.42  Cooper               : 0.00
% 2.82/1.42  Total                : 0.68
% 2.82/1.42  Index Insertion      : 0.00
% 2.82/1.42  Index Deletion       : 0.00
% 2.82/1.42  Index Matching       : 0.00
% 2.82/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
