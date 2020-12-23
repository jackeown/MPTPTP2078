%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:15 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 206 expanded)
%              Number of leaves         :   36 (  89 expanded)
%              Depth                    :   14
%              Number of atoms          :  219 ( 734 expanded)
%              Number of equality atoms :   33 (  83 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k7_partfun1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_partfun1,type,(
    k7_partfun1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k8_funct_2,type,(
    k8_funct_2: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_156,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C,D] :
                ( ( v1_funct_1(D)
                  & v1_funct_2(D,B,A)
                  & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
               => ! [E] :
                    ( ( v1_funct_1(E)
                      & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,C))) )
                   => ! [F] :
                        ( m1_subset_1(F,B)
                       => ( v1_partfun1(E,A)
                         => k3_funct_2(B,C,k8_funct_2(B,A,C,D,E),F) = k7_partfun1(C,E,k3_funct_2(B,A,D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t193_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_103,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_129,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C,D] :
              ( ( v1_funct_1(D)
                & v1_funct_2(D,B,A)
                & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
             => ! [E] :
                  ( ( v1_funct_1(E)
                    & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,C))) )
                 => ! [F] :
                      ( m1_subset_1(F,B)
                     => ( v1_partfun1(E,A)
                       => k3_funct_2(B,C,k8_funct_2(B,A,C,D,E),F) = k1_funct_1(E,k3_funct_2(B,A,D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_funct_2)).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_32,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_71,plain,(
    ! [C_102,B_103,A_104] :
      ( v5_relat_1(C_102,B_103)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_104,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_79,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_71])).

tff(c_6,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_48,plain,(
    ! [B_95,A_96] :
      ( v1_relat_1(B_95)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(A_96))
      | ~ v1_relat_1(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_51,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_38,c_48])).

tff(c_57,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_51])).

tff(c_78,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_71])).

tff(c_42,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_46,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_62,plain,(
    ! [C_99,A_100,B_101] :
      ( v4_relat_1(C_99,A_100)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_69,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_62])).

tff(c_81,plain,(
    ! [B_106,A_107] :
      ( k1_relat_1(B_106) = A_107
      | ~ v1_partfun1(B_106,A_107)
      | ~ v4_relat_1(B_106,A_107)
      | ~ v1_relat_1(B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_87,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ v1_partfun1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_69,c_81])).

tff(c_93,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ v1_partfun1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_87])).

tff(c_103,plain,(
    ~ v1_partfun1('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_93])).

tff(c_40,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_105,plain,(
    ! [C_111,A_112,B_113] :
      ( v1_partfun1(C_111,A_112)
      | ~ v1_funct_2(C_111,A_112,B_113)
      | ~ v1_funct_1(C_111)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113)))
      | v1_xboole_0(B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_108,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_105])).

tff(c_114,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_108])).

tff(c_116,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_103,c_114])).

tff(c_117,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_8,plain,(
    ! [B_9,C_11,A_8] :
      ( r2_hidden(k1_funct_1(B_9,C_11),A_8)
      | ~ r2_hidden(C_11,k1_relat_1(B_9))
      | ~ v1_funct_1(B_9)
      | ~ v5_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_54,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_48])).

tff(c_60,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_54])).

tff(c_36,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_30,plain,(
    v1_partfun1('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_70,plain,(
    v4_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_62])).

tff(c_84,plain,
    ( k1_relat_1('#skF_5') = '#skF_1'
    | ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_81])).

tff(c_90,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_30,c_84])).

tff(c_144,plain,(
    ! [A_120,B_121,C_122] :
      ( k7_partfun1(A_120,B_121,C_122) = k1_funct_1(B_121,C_122)
      | ~ r2_hidden(C_122,k1_relat_1(B_121))
      | ~ v1_funct_1(B_121)
      | ~ v5_relat_1(B_121,A_120)
      | ~ v1_relat_1(B_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_151,plain,(
    ! [A_120,C_122] :
      ( k7_partfun1(A_120,'#skF_5',C_122) = k1_funct_1('#skF_5',C_122)
      | ~ r2_hidden(C_122,'#skF_1')
      | ~ v1_funct_1('#skF_5')
      | ~ v5_relat_1('#skF_5',A_120)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_144])).

tff(c_184,plain,(
    ! [A_129,C_130] :
      ( k7_partfun1(A_129,'#skF_5',C_130) = k1_funct_1('#skF_5',C_130)
      | ~ r2_hidden(C_130,'#skF_1')
      | ~ v5_relat_1('#skF_5',A_129) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_36,c_151])).

tff(c_271,plain,(
    ! [A_151,B_152,C_153] :
      ( k7_partfun1(A_151,'#skF_5',k1_funct_1(B_152,C_153)) = k1_funct_1('#skF_5',k1_funct_1(B_152,C_153))
      | ~ v5_relat_1('#skF_5',A_151)
      | ~ r2_hidden(C_153,k1_relat_1(B_152))
      | ~ v1_funct_1(B_152)
      | ~ v5_relat_1(B_152,'#skF_1')
      | ~ v1_relat_1(B_152) ) ),
    inference(resolution,[status(thm)],[c_8,c_184])).

tff(c_276,plain,(
    ! [A_151,C_153] :
      ( k7_partfun1(A_151,'#skF_5',k1_funct_1('#skF_4',C_153)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',C_153))
      | ~ v5_relat_1('#skF_5',A_151)
      | ~ r2_hidden(C_153,'#skF_2')
      | ~ v1_funct_1('#skF_4')
      | ~ v5_relat_1('#skF_4','#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_271])).

tff(c_284,plain,(
    ! [A_151,C_153] :
      ( k7_partfun1(A_151,'#skF_5',k1_funct_1('#skF_4',C_153)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',C_153))
      | ~ v5_relat_1('#skF_5',A_151)
      | ~ r2_hidden(C_153,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_78,c_42,c_276])).

tff(c_172,plain,(
    ! [A_125,B_126,C_127,D_128] :
      ( k3_funct_2(A_125,B_126,C_127,D_128) = k1_funct_1(C_127,D_128)
      | ~ m1_subset_1(D_128,A_125)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126)))
      | ~ v1_funct_2(C_127,A_125,B_126)
      | ~ v1_funct_1(C_127)
      | v1_xboole_0(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_178,plain,(
    ! [B_126,C_127] :
      ( k3_funct_2('#skF_2',B_126,C_127,'#skF_6') = k1_funct_1(C_127,'#skF_6')
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_126)))
      | ~ v1_funct_2(C_127,'#skF_2',B_126)
      | ~ v1_funct_1(C_127)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_32,c_172])).

tff(c_213,plain,(
    ! [B_137,C_138] :
      ( k3_funct_2('#skF_2',B_137,C_138,'#skF_6') = k1_funct_1(C_138,'#skF_6')
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_137)))
      | ~ v1_funct_2(C_138,'#skF_2',B_137)
      | ~ v1_funct_1(C_138) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_178])).

tff(c_216,plain,
    ( k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_213])).

tff(c_219,plain,(
    k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_216])).

tff(c_225,plain,(
    ! [B_140,D_144,A_143,F_142,C_141,E_139] :
      ( k3_funct_2(B_140,C_141,k8_funct_2(B_140,A_143,C_141,D_144,E_139),F_142) = k1_funct_1(E_139,k3_funct_2(B_140,A_143,D_144,F_142))
      | ~ v1_partfun1(E_139,A_143)
      | ~ m1_subset_1(F_142,B_140)
      | ~ m1_subset_1(E_139,k1_zfmisc_1(k2_zfmisc_1(A_143,C_141)))
      | ~ v1_funct_1(E_139)
      | ~ m1_subset_1(D_144,k1_zfmisc_1(k2_zfmisc_1(B_140,A_143)))
      | ~ v1_funct_2(D_144,B_140,A_143)
      | ~ v1_funct_1(D_144)
      | v1_xboole_0(B_140)
      | v1_xboole_0(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_229,plain,(
    ! [B_140,D_144,F_142] :
      ( k3_funct_2(B_140,'#skF_3',k8_funct_2(B_140,'#skF_1','#skF_3',D_144,'#skF_5'),F_142) = k1_funct_1('#skF_5',k3_funct_2(B_140,'#skF_1',D_144,F_142))
      | ~ v1_partfun1('#skF_5','#skF_1')
      | ~ m1_subset_1(F_142,B_140)
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_144,k1_zfmisc_1(k2_zfmisc_1(B_140,'#skF_1')))
      | ~ v1_funct_2(D_144,B_140,'#skF_1')
      | ~ v1_funct_1(D_144)
      | v1_xboole_0(B_140)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_34,c_225])).

tff(c_236,plain,(
    ! [B_140,D_144,F_142] :
      ( k3_funct_2(B_140,'#skF_3',k8_funct_2(B_140,'#skF_1','#skF_3',D_144,'#skF_5'),F_142) = k1_funct_1('#skF_5',k3_funct_2(B_140,'#skF_1',D_144,F_142))
      | ~ m1_subset_1(F_142,B_140)
      | ~ m1_subset_1(D_144,k1_zfmisc_1(k2_zfmisc_1(B_140,'#skF_1')))
      | ~ v1_funct_2(D_144,B_140,'#skF_1')
      | ~ v1_funct_1(D_144)
      | v1_xboole_0(B_140)
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30,c_229])).

tff(c_315,plain,(
    ! [B_160,D_161,F_162] :
      ( k3_funct_2(B_160,'#skF_3',k8_funct_2(B_160,'#skF_1','#skF_3',D_161,'#skF_5'),F_162) = k1_funct_1('#skF_5',k3_funct_2(B_160,'#skF_1',D_161,F_162))
      | ~ m1_subset_1(F_162,B_160)
      | ~ m1_subset_1(D_161,k1_zfmisc_1(k2_zfmisc_1(B_160,'#skF_1')))
      | ~ v1_funct_2(D_161,B_160,'#skF_1')
      | ~ v1_funct_1(D_161)
      | v1_xboole_0(B_160) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_236])).

tff(c_317,plain,(
    ! [F_162] :
      ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_162) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',F_162))
      | ~ m1_subset_1(F_162,'#skF_2')
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_38,c_315])).

tff(c_320,plain,(
    ! [F_162] :
      ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_162) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',F_162))
      | ~ m1_subset_1(F_162,'#skF_2')
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_317])).

tff(c_322,plain,(
    ! [F_163] :
      ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_163) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',F_163))
      | ~ m1_subset_1(F_163,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_320])).

tff(c_28,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k7_partfun1('#skF_3','#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_220,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_28])).

tff(c_328,plain,
    ( k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) != k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6'))
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_322,c_220])).

tff(c_334,plain,(
    k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_219,c_328])).

tff(c_338,plain,
    ( ~ v5_relat_1('#skF_5','#skF_3')
    | ~ r2_hidden('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_284,c_334])).

tff(c_341,plain,(
    ~ r2_hidden('#skF_6','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_338])).

tff(c_344,plain,
    ( v1_xboole_0('#skF_2')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_341])).

tff(c_347,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_344])).

tff(c_349,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_347])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:26:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.66/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.33  
% 2.66/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.34  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k7_partfun1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.66/1.34  
% 2.66/1.34  %Foreground sorts:
% 2.66/1.34  
% 2.66/1.34  
% 2.66/1.34  %Background operators:
% 2.66/1.34  
% 2.66/1.34  
% 2.66/1.34  %Foreground operators:
% 2.66/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.66/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.66/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.66/1.34  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 2.66/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.66/1.34  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.66/1.34  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 2.66/1.34  tff('#skF_6', type, '#skF_6': $i).
% 2.66/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.66/1.34  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.66/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.66/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.66/1.34  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.66/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.66/1.34  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.66/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.66/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.66/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.66/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.66/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.66/1.34  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.66/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.66/1.34  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.66/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.66/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.66/1.34  
% 2.66/1.36  tff(f_156, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C)))) => (![F]: (m1_subset_1(F, B) => (v1_partfun1(E, A) => (k3_funct_2(B, C, k8_funct_2(B, A, C, D, E), F) = k7_partfun1(C, E, k3_funct_2(B, A, D, F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t193_funct_2)).
% 2.66/1.36  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.66/1.36  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.66/1.36  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.66/1.36  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.66/1.36  tff(f_79, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 2.66/1.36  tff(f_71, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.66/1.36  tff(f_51, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_1)).
% 2.66/1.36  tff(f_90, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_partfun1)).
% 2.66/1.36  tff(f_103, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.66/1.36  tff(f_129, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C)))) => (![F]: (m1_subset_1(F, B) => (v1_partfun1(E, A) => (k3_funct_2(B, C, k8_funct_2(B, A, C, D, E), F) = k1_funct_1(E, k3_funct_2(B, A, D, F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t192_funct_2)).
% 2.66/1.36  tff(c_44, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.66/1.36  tff(c_32, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.66/1.36  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.66/1.36  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.66/1.36  tff(c_71, plain, (![C_102, B_103, A_104]: (v5_relat_1(C_102, B_103) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_104, B_103))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.66/1.36  tff(c_79, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_71])).
% 2.66/1.36  tff(c_6, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.66/1.36  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.66/1.36  tff(c_48, plain, (![B_95, A_96]: (v1_relat_1(B_95) | ~m1_subset_1(B_95, k1_zfmisc_1(A_96)) | ~v1_relat_1(A_96))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.66/1.36  tff(c_51, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_38, c_48])).
% 2.66/1.36  tff(c_57, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_51])).
% 2.66/1.36  tff(c_78, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_38, c_71])).
% 2.66/1.36  tff(c_42, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.66/1.36  tff(c_46, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.66/1.36  tff(c_62, plain, (![C_99, A_100, B_101]: (v4_relat_1(C_99, A_100) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.66/1.36  tff(c_69, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_62])).
% 2.66/1.36  tff(c_81, plain, (![B_106, A_107]: (k1_relat_1(B_106)=A_107 | ~v1_partfun1(B_106, A_107) | ~v4_relat_1(B_106, A_107) | ~v1_relat_1(B_106))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.66/1.36  tff(c_87, plain, (k1_relat_1('#skF_4')='#skF_2' | ~v1_partfun1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_69, c_81])).
% 2.66/1.36  tff(c_93, plain, (k1_relat_1('#skF_4')='#skF_2' | ~v1_partfun1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_57, c_87])).
% 2.66/1.36  tff(c_103, plain, (~v1_partfun1('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_93])).
% 2.66/1.36  tff(c_40, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.66/1.36  tff(c_105, plain, (![C_111, A_112, B_113]: (v1_partfun1(C_111, A_112) | ~v1_funct_2(C_111, A_112, B_113) | ~v1_funct_1(C_111) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))) | v1_xboole_0(B_113))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.66/1.36  tff(c_108, plain, (v1_partfun1('#skF_4', '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_105])).
% 2.66/1.36  tff(c_114, plain, (v1_partfun1('#skF_4', '#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_108])).
% 2.66/1.36  tff(c_116, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_103, c_114])).
% 2.66/1.36  tff(c_117, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_93])).
% 2.66/1.36  tff(c_8, plain, (![B_9, C_11, A_8]: (r2_hidden(k1_funct_1(B_9, C_11), A_8) | ~r2_hidden(C_11, k1_relat_1(B_9)) | ~v1_funct_1(B_9) | ~v5_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.66/1.36  tff(c_54, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_34, c_48])).
% 2.66/1.36  tff(c_60, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_54])).
% 2.66/1.36  tff(c_36, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.66/1.36  tff(c_30, plain, (v1_partfun1('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.66/1.36  tff(c_70, plain, (v4_relat_1('#skF_5', '#skF_1')), inference(resolution, [status(thm)], [c_34, c_62])).
% 2.66/1.36  tff(c_84, plain, (k1_relat_1('#skF_5')='#skF_1' | ~v1_partfun1('#skF_5', '#skF_1') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_70, c_81])).
% 2.66/1.36  tff(c_90, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_30, c_84])).
% 2.66/1.36  tff(c_144, plain, (![A_120, B_121, C_122]: (k7_partfun1(A_120, B_121, C_122)=k1_funct_1(B_121, C_122) | ~r2_hidden(C_122, k1_relat_1(B_121)) | ~v1_funct_1(B_121) | ~v5_relat_1(B_121, A_120) | ~v1_relat_1(B_121))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.66/1.36  tff(c_151, plain, (![A_120, C_122]: (k7_partfun1(A_120, '#skF_5', C_122)=k1_funct_1('#skF_5', C_122) | ~r2_hidden(C_122, '#skF_1') | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', A_120) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_90, c_144])).
% 2.66/1.36  tff(c_184, plain, (![A_129, C_130]: (k7_partfun1(A_129, '#skF_5', C_130)=k1_funct_1('#skF_5', C_130) | ~r2_hidden(C_130, '#skF_1') | ~v5_relat_1('#skF_5', A_129))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_36, c_151])).
% 2.66/1.36  tff(c_271, plain, (![A_151, B_152, C_153]: (k7_partfun1(A_151, '#skF_5', k1_funct_1(B_152, C_153))=k1_funct_1('#skF_5', k1_funct_1(B_152, C_153)) | ~v5_relat_1('#skF_5', A_151) | ~r2_hidden(C_153, k1_relat_1(B_152)) | ~v1_funct_1(B_152) | ~v5_relat_1(B_152, '#skF_1') | ~v1_relat_1(B_152))), inference(resolution, [status(thm)], [c_8, c_184])).
% 2.66/1.36  tff(c_276, plain, (![A_151, C_153]: (k7_partfun1(A_151, '#skF_5', k1_funct_1('#skF_4', C_153))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', C_153)) | ~v5_relat_1('#skF_5', A_151) | ~r2_hidden(C_153, '#skF_2') | ~v1_funct_1('#skF_4') | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_117, c_271])).
% 2.66/1.36  tff(c_284, plain, (![A_151, C_153]: (k7_partfun1(A_151, '#skF_5', k1_funct_1('#skF_4', C_153))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', C_153)) | ~v5_relat_1('#skF_5', A_151) | ~r2_hidden(C_153, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_78, c_42, c_276])).
% 2.66/1.36  tff(c_172, plain, (![A_125, B_126, C_127, D_128]: (k3_funct_2(A_125, B_126, C_127, D_128)=k1_funct_1(C_127, D_128) | ~m1_subset_1(D_128, A_125) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))) | ~v1_funct_2(C_127, A_125, B_126) | ~v1_funct_1(C_127) | v1_xboole_0(A_125))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.66/1.36  tff(c_178, plain, (![B_126, C_127]: (k3_funct_2('#skF_2', B_126, C_127, '#skF_6')=k1_funct_1(C_127, '#skF_6') | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_126))) | ~v1_funct_2(C_127, '#skF_2', B_126) | ~v1_funct_1(C_127) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_172])).
% 2.66/1.36  tff(c_213, plain, (![B_137, C_138]: (k3_funct_2('#skF_2', B_137, C_138, '#skF_6')=k1_funct_1(C_138, '#skF_6') | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_137))) | ~v1_funct_2(C_138, '#skF_2', B_137) | ~v1_funct_1(C_138))), inference(negUnitSimplification, [status(thm)], [c_44, c_178])).
% 2.66/1.36  tff(c_216, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_213])).
% 2.66/1.36  tff(c_219, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_216])).
% 2.66/1.36  tff(c_225, plain, (![B_140, D_144, A_143, F_142, C_141, E_139]: (k3_funct_2(B_140, C_141, k8_funct_2(B_140, A_143, C_141, D_144, E_139), F_142)=k1_funct_1(E_139, k3_funct_2(B_140, A_143, D_144, F_142)) | ~v1_partfun1(E_139, A_143) | ~m1_subset_1(F_142, B_140) | ~m1_subset_1(E_139, k1_zfmisc_1(k2_zfmisc_1(A_143, C_141))) | ~v1_funct_1(E_139) | ~m1_subset_1(D_144, k1_zfmisc_1(k2_zfmisc_1(B_140, A_143))) | ~v1_funct_2(D_144, B_140, A_143) | ~v1_funct_1(D_144) | v1_xboole_0(B_140) | v1_xboole_0(A_143))), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.66/1.36  tff(c_229, plain, (![B_140, D_144, F_142]: (k3_funct_2(B_140, '#skF_3', k8_funct_2(B_140, '#skF_1', '#skF_3', D_144, '#skF_5'), F_142)=k1_funct_1('#skF_5', k3_funct_2(B_140, '#skF_1', D_144, F_142)) | ~v1_partfun1('#skF_5', '#skF_1') | ~m1_subset_1(F_142, B_140) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_144, k1_zfmisc_1(k2_zfmisc_1(B_140, '#skF_1'))) | ~v1_funct_2(D_144, B_140, '#skF_1') | ~v1_funct_1(D_144) | v1_xboole_0(B_140) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_34, c_225])).
% 2.66/1.36  tff(c_236, plain, (![B_140, D_144, F_142]: (k3_funct_2(B_140, '#skF_3', k8_funct_2(B_140, '#skF_1', '#skF_3', D_144, '#skF_5'), F_142)=k1_funct_1('#skF_5', k3_funct_2(B_140, '#skF_1', D_144, F_142)) | ~m1_subset_1(F_142, B_140) | ~m1_subset_1(D_144, k1_zfmisc_1(k2_zfmisc_1(B_140, '#skF_1'))) | ~v1_funct_2(D_144, B_140, '#skF_1') | ~v1_funct_1(D_144) | v1_xboole_0(B_140) | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_30, c_229])).
% 2.66/1.36  tff(c_315, plain, (![B_160, D_161, F_162]: (k3_funct_2(B_160, '#skF_3', k8_funct_2(B_160, '#skF_1', '#skF_3', D_161, '#skF_5'), F_162)=k1_funct_1('#skF_5', k3_funct_2(B_160, '#skF_1', D_161, F_162)) | ~m1_subset_1(F_162, B_160) | ~m1_subset_1(D_161, k1_zfmisc_1(k2_zfmisc_1(B_160, '#skF_1'))) | ~v1_funct_2(D_161, B_160, '#skF_1') | ~v1_funct_1(D_161) | v1_xboole_0(B_160))), inference(negUnitSimplification, [status(thm)], [c_46, c_236])).
% 2.66/1.36  tff(c_317, plain, (![F_162]: (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_162)=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', F_162)) | ~m1_subset_1(F_162, '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_315])).
% 2.66/1.36  tff(c_320, plain, (![F_162]: (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_162)=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', F_162)) | ~m1_subset_1(F_162, '#skF_2') | v1_xboole_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_317])).
% 2.66/1.36  tff(c_322, plain, (![F_163]: (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_163)=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', F_163)) | ~m1_subset_1(F_163, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_44, c_320])).
% 2.66/1.36  tff(c_28, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k7_partfun1('#skF_3', '#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.66/1.36  tff(c_220, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_219, c_28])).
% 2.66/1.36  tff(c_328, plain, (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))!=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')) | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_322, c_220])).
% 2.66/1.36  tff(c_334, plain, (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_219, c_328])).
% 2.66/1.36  tff(c_338, plain, (~v5_relat_1('#skF_5', '#skF_3') | ~r2_hidden('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_284, c_334])).
% 2.66/1.36  tff(c_341, plain, (~r2_hidden('#skF_6', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_338])).
% 2.66/1.36  tff(c_344, plain, (v1_xboole_0('#skF_2') | ~m1_subset_1('#skF_6', '#skF_2')), inference(resolution, [status(thm)], [c_2, c_341])).
% 2.66/1.36  tff(c_347, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_344])).
% 2.66/1.36  tff(c_349, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_347])).
% 2.66/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.36  
% 2.66/1.36  Inference rules
% 2.66/1.36  ----------------------
% 2.66/1.36  #Ref     : 0
% 2.66/1.36  #Sup     : 61
% 2.66/1.36  #Fact    : 0
% 2.66/1.36  #Define  : 0
% 2.66/1.36  #Split   : 5
% 2.66/1.36  #Chain   : 0
% 2.66/1.36  #Close   : 0
% 2.66/1.36  
% 2.66/1.36  Ordering : KBO
% 2.66/1.36  
% 2.66/1.36  Simplification rules
% 2.66/1.36  ----------------------
% 2.66/1.36  #Subsume      : 2
% 2.66/1.36  #Demod        : 58
% 2.66/1.36  #Tautology    : 17
% 2.66/1.36  #SimpNegUnit  : 11
% 2.66/1.36  #BackRed      : 1
% 2.66/1.36  
% 2.66/1.36  #Partial instantiations: 0
% 2.66/1.36  #Strategies tried      : 1
% 2.66/1.36  
% 2.66/1.36  Timing (in seconds)
% 2.66/1.36  ----------------------
% 2.66/1.36  Preprocessing        : 0.34
% 2.66/1.36  Parsing              : 0.18
% 2.66/1.36  CNF conversion       : 0.03
% 2.66/1.36  Main loop            : 0.25
% 2.66/1.36  Inferencing          : 0.09
% 2.66/1.36  Reduction            : 0.08
% 2.66/1.36  Demodulation         : 0.05
% 2.66/1.36  BG Simplification    : 0.02
% 2.82/1.36  Subsumption          : 0.04
% 2.82/1.36  Abstraction          : 0.01
% 2.82/1.36  MUC search           : 0.00
% 2.82/1.36  Cooper               : 0.00
% 2.82/1.36  Total                : 0.62
% 2.82/1.36  Index Insertion      : 0.00
% 2.82/1.36  Index Deletion       : 0.00
% 2.82/1.36  Index Matching       : 0.00
% 2.82/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
