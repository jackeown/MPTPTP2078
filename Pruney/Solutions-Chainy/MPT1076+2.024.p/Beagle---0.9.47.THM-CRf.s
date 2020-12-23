%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:15 EST 2020

% Result     : Theorem 3.31s
% Output     : CNFRefutation 3.38s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 213 expanded)
%              Number of leaves         :   36 (  91 expanded)
%              Depth                    :   15
%              Number of atoms          :  224 ( 756 expanded)
%              Number of equality atoms :   35 (  86 expanded)
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

tff(f_155,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

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

tff(f_78,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v5_relat_1(C,A)
        & v1_funct_1(C) )
     => ( r2_hidden(B,k1_relat_1(C))
       => m1_subset_1(k1_funct_1(C,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_102,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_128,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_funct_2)).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_32,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_71,plain,(
    ! [C_101,B_102,A_103] :
      ( v5_relat_1(C_101,B_102)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_103,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_78,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_71])).

tff(c_6,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_48,plain,(
    ! [B_94,A_95] :
      ( v1_relat_1(B_94)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(A_95))
      | ~ v1_relat_1(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_51,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_38,c_48])).

tff(c_57,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_51])).

tff(c_42,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_46,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_62,plain,(
    ! [C_98,A_99,B_100] :
      ( v4_relat_1(C_98,A_99)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_69,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_62])).

tff(c_81,plain,(
    ! [B_105,A_106] :
      ( k1_relat_1(B_105) = A_106
      | ~ v1_partfun1(B_105,A_106)
      | ~ v4_relat_1(B_105,A_106)
      | ~ v1_relat_1(B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

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
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_133,plain,(
    ! [C_119,A_120,B_121] :
      ( v1_partfun1(C_119,A_120)
      | ~ v1_funct_2(C_119,A_120,B_121)
      | ~ v1_funct_1(C_119)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121)))
      | v1_xboole_0(B_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_140,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_133])).

tff(c_147,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_140])).

tff(c_149,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_103,c_147])).

tff(c_150,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_161,plain,(
    ! [C_122,B_123,A_124] :
      ( m1_subset_1(k1_funct_1(C_122,B_123),A_124)
      | ~ r2_hidden(B_123,k1_relat_1(C_122))
      | ~ v1_funct_1(C_122)
      | ~ v5_relat_1(C_122,A_124)
      | ~ v1_relat_1(C_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_163,plain,(
    ! [B_123,A_124] :
      ( m1_subset_1(k1_funct_1('#skF_4',B_123),A_124)
      | ~ r2_hidden(B_123,'#skF_2')
      | ~ v1_funct_1('#skF_4')
      | ~ v5_relat_1('#skF_4',A_124)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_161])).

tff(c_170,plain,(
    ! [B_123,A_124] :
      ( m1_subset_1(k1_funct_1('#skF_4',B_123),A_124)
      | ~ r2_hidden(B_123,'#skF_2')
      | ~ v5_relat_1('#skF_4',A_124) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_42,c_163])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_79,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_71])).

tff(c_54,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_48])).

tff(c_60,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_54])).

tff(c_36,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_30,plain,(
    v1_partfun1('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

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

tff(c_239,plain,(
    ! [A_146,B_147,C_148] :
      ( k7_partfun1(A_146,B_147,C_148) = k1_funct_1(B_147,C_148)
      | ~ r2_hidden(C_148,k1_relat_1(B_147))
      | ~ v1_funct_1(B_147)
      | ~ v5_relat_1(B_147,A_146)
      | ~ v1_relat_1(B_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_243,plain,(
    ! [A_146,C_148] :
      ( k7_partfun1(A_146,'#skF_5',C_148) = k1_funct_1('#skF_5',C_148)
      | ~ r2_hidden(C_148,'#skF_1')
      | ~ v1_funct_1('#skF_5')
      | ~ v5_relat_1('#skF_5',A_146)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_239])).

tff(c_252,plain,(
    ! [A_149,C_150] :
      ( k7_partfun1(A_149,'#skF_5',C_150) = k1_funct_1('#skF_5',C_150)
      | ~ r2_hidden(C_150,'#skF_1')
      | ~ v5_relat_1('#skF_5',A_149) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_36,c_243])).

tff(c_255,plain,(
    ! [A_149,A_1] :
      ( k7_partfun1(A_149,'#skF_5',A_1) = k1_funct_1('#skF_5',A_1)
      | ~ v5_relat_1('#skF_5',A_149)
      | v1_xboole_0('#skF_1')
      | ~ m1_subset_1(A_1,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_2,c_252])).

tff(c_266,plain,(
    ! [A_153,A_154] :
      ( k7_partfun1(A_153,'#skF_5',A_154) = k1_funct_1('#skF_5',A_154)
      | ~ v5_relat_1('#skF_5',A_153)
      | ~ m1_subset_1(A_154,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_255])).

tff(c_270,plain,(
    ! [A_155] :
      ( k7_partfun1('#skF_3','#skF_5',A_155) = k1_funct_1('#skF_5',A_155)
      | ~ m1_subset_1(A_155,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_79,c_266])).

tff(c_278,plain,(
    ! [B_123] :
      ( k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4',B_123)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',B_123))
      | ~ r2_hidden(B_123,'#skF_2')
      | ~ v5_relat_1('#skF_4','#skF_1') ) ),
    inference(resolution,[status(thm)],[c_170,c_270])).

tff(c_282,plain,(
    ! [B_123] :
      ( k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4',B_123)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',B_123))
      | ~ r2_hidden(B_123,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_278])).

tff(c_302,plain,(
    ! [A_159,B_160,C_161,D_162] :
      ( k3_funct_2(A_159,B_160,C_161,D_162) = k1_funct_1(C_161,D_162)
      | ~ m1_subset_1(D_162,A_159)
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(A_159,B_160)))
      | ~ v1_funct_2(C_161,A_159,B_160)
      | ~ v1_funct_1(C_161)
      | v1_xboole_0(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_312,plain,(
    ! [B_160,C_161] :
      ( k3_funct_2('#skF_2',B_160,C_161,'#skF_6') = k1_funct_1(C_161,'#skF_6')
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_160)))
      | ~ v1_funct_2(C_161,'#skF_2',B_160)
      | ~ v1_funct_1(C_161)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_32,c_302])).

tff(c_334,plain,(
    ! [B_164,C_165] :
      ( k3_funct_2('#skF_2',B_164,C_165,'#skF_6') = k1_funct_1(C_165,'#skF_6')
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_164)))
      | ~ v1_funct_2(C_165,'#skF_2',B_164)
      | ~ v1_funct_1(C_165) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_312])).

tff(c_345,plain,
    ( k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_334])).

tff(c_350,plain,(
    k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_345])).

tff(c_357,plain,(
    ! [D_170,C_166,B_167,F_168,A_169,E_171] :
      ( k3_funct_2(B_167,C_166,k8_funct_2(B_167,A_169,C_166,D_170,E_171),F_168) = k1_funct_1(E_171,k3_funct_2(B_167,A_169,D_170,F_168))
      | ~ v1_partfun1(E_171,A_169)
      | ~ m1_subset_1(F_168,B_167)
      | ~ m1_subset_1(E_171,k1_zfmisc_1(k2_zfmisc_1(A_169,C_166)))
      | ~ v1_funct_1(E_171)
      | ~ m1_subset_1(D_170,k1_zfmisc_1(k2_zfmisc_1(B_167,A_169)))
      | ~ v1_funct_2(D_170,B_167,A_169)
      | ~ v1_funct_1(D_170)
      | v1_xboole_0(B_167)
      | v1_xboole_0(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_367,plain,(
    ! [B_167,D_170,F_168] :
      ( k3_funct_2(B_167,'#skF_3',k8_funct_2(B_167,'#skF_1','#skF_3',D_170,'#skF_5'),F_168) = k1_funct_1('#skF_5',k3_funct_2(B_167,'#skF_1',D_170,F_168))
      | ~ v1_partfun1('#skF_5','#skF_1')
      | ~ m1_subset_1(F_168,B_167)
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_170,k1_zfmisc_1(k2_zfmisc_1(B_167,'#skF_1')))
      | ~ v1_funct_2(D_170,B_167,'#skF_1')
      | ~ v1_funct_1(D_170)
      | v1_xboole_0(B_167)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_34,c_357])).

tff(c_376,plain,(
    ! [B_167,D_170,F_168] :
      ( k3_funct_2(B_167,'#skF_3',k8_funct_2(B_167,'#skF_1','#skF_3',D_170,'#skF_5'),F_168) = k1_funct_1('#skF_5',k3_funct_2(B_167,'#skF_1',D_170,F_168))
      | ~ m1_subset_1(F_168,B_167)
      | ~ m1_subset_1(D_170,k1_zfmisc_1(k2_zfmisc_1(B_167,'#skF_1')))
      | ~ v1_funct_2(D_170,B_167,'#skF_1')
      | ~ v1_funct_1(D_170)
      | v1_xboole_0(B_167)
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30,c_367])).

tff(c_439,plain,(
    ! [B_189,D_190,F_191] :
      ( k3_funct_2(B_189,'#skF_3',k8_funct_2(B_189,'#skF_1','#skF_3',D_190,'#skF_5'),F_191) = k1_funct_1('#skF_5',k3_funct_2(B_189,'#skF_1',D_190,F_191))
      | ~ m1_subset_1(F_191,B_189)
      | ~ m1_subset_1(D_190,k1_zfmisc_1(k2_zfmisc_1(B_189,'#skF_1')))
      | ~ v1_funct_2(D_190,B_189,'#skF_1')
      | ~ v1_funct_1(D_190)
      | v1_xboole_0(B_189) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_376])).

tff(c_450,plain,(
    ! [F_191] :
      ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_191) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',F_191))
      | ~ m1_subset_1(F_191,'#skF_2')
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_38,c_439])).

tff(c_456,plain,(
    ! [F_191] :
      ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_191) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',F_191))
      | ~ m1_subset_1(F_191,'#skF_2')
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_450])).

tff(c_458,plain,(
    ! [F_192] :
      ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_192) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',F_192))
      | ~ m1_subset_1(F_192,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_456])).

tff(c_28,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k7_partfun1('#skF_3','#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_351,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_350,c_28])).

tff(c_464,plain,
    ( k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) != k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6'))
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_458,c_351])).

tff(c_470,plain,(
    k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_350,c_464])).

tff(c_475,plain,(
    ~ r2_hidden('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_282,c_470])).

tff(c_478,plain,
    ( v1_xboole_0('#skF_2')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_475])).

tff(c_481,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_478])).

tff(c_483,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_481])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:26:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.31/1.75  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.38/1.76  
% 3.38/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.38/1.77  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k7_partfun1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.38/1.77  
% 3.38/1.77  %Foreground sorts:
% 3.38/1.77  
% 3.38/1.77  
% 3.38/1.77  %Background operators:
% 3.38/1.77  
% 3.38/1.77  
% 3.38/1.77  %Foreground operators:
% 3.38/1.77  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.38/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.38/1.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.38/1.77  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 3.38/1.77  tff('#skF_5', type, '#skF_5': $i).
% 3.38/1.77  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.38/1.77  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 3.38/1.77  tff('#skF_6', type, '#skF_6': $i).
% 3.38/1.77  tff('#skF_2', type, '#skF_2': $i).
% 3.38/1.77  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.38/1.77  tff('#skF_3', type, '#skF_3': $i).
% 3.38/1.77  tff('#skF_1', type, '#skF_1': $i).
% 3.38/1.77  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.38/1.77  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.38/1.77  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.38/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.38/1.77  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.38/1.77  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.38/1.77  tff('#skF_4', type, '#skF_4': $i).
% 3.38/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.38/1.77  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.38/1.77  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.38/1.77  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 3.38/1.77  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.38/1.77  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.38/1.77  
% 3.38/1.79  tff(f_155, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C)))) => (![F]: (m1_subset_1(F, B) => (v1_partfun1(E, A) => (k3_funct_2(B, C, k8_funct_2(B, A, C, D, E), F) = k7_partfun1(C, E, k3_funct_2(B, A, D, F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t193_funct_2)).
% 3.38/1.79  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.38/1.79  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.38/1.79  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.38/1.79  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.38/1.79  tff(f_78, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 3.38/1.79  tff(f_70, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 3.38/1.79  tff(f_50, axiom, (![A, B, C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (r2_hidden(B, k1_relat_1(C)) => m1_subset_1(k1_funct_1(C, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_funct_1)).
% 3.38/1.79  tff(f_89, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 3.38/1.79  tff(f_102, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 3.38/1.79  tff(f_128, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C)))) => (![F]: (m1_subset_1(F, B) => (v1_partfun1(E, A) => (k3_funct_2(B, C, k8_funct_2(B, A, C, D, E), F) = k1_funct_1(E, k3_funct_2(B, A, D, F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_funct_2)).
% 3.38/1.79  tff(c_44, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_155])).
% 3.38/1.79  tff(c_32, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_155])).
% 3.38/1.79  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.38/1.79  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_155])).
% 3.38/1.79  tff(c_71, plain, (![C_101, B_102, A_103]: (v5_relat_1(C_101, B_102) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_103, B_102))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.38/1.79  tff(c_78, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_38, c_71])).
% 3.38/1.79  tff(c_6, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.38/1.79  tff(c_48, plain, (![B_94, A_95]: (v1_relat_1(B_94) | ~m1_subset_1(B_94, k1_zfmisc_1(A_95)) | ~v1_relat_1(A_95))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.38/1.79  tff(c_51, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_38, c_48])).
% 3.38/1.79  tff(c_57, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_51])).
% 3.38/1.79  tff(c_42, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_155])).
% 3.38/1.79  tff(c_46, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_155])).
% 3.38/1.79  tff(c_62, plain, (![C_98, A_99, B_100]: (v4_relat_1(C_98, A_99) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.38/1.79  tff(c_69, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_62])).
% 3.38/1.79  tff(c_81, plain, (![B_105, A_106]: (k1_relat_1(B_105)=A_106 | ~v1_partfun1(B_105, A_106) | ~v4_relat_1(B_105, A_106) | ~v1_relat_1(B_105))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.38/1.79  tff(c_87, plain, (k1_relat_1('#skF_4')='#skF_2' | ~v1_partfun1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_69, c_81])).
% 3.38/1.79  tff(c_93, plain, (k1_relat_1('#skF_4')='#skF_2' | ~v1_partfun1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_57, c_87])).
% 3.38/1.79  tff(c_103, plain, (~v1_partfun1('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_93])).
% 3.38/1.79  tff(c_40, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_155])).
% 3.38/1.79  tff(c_133, plain, (![C_119, A_120, B_121]: (v1_partfun1(C_119, A_120) | ~v1_funct_2(C_119, A_120, B_121) | ~v1_funct_1(C_119) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))) | v1_xboole_0(B_121))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.38/1.79  tff(c_140, plain, (v1_partfun1('#skF_4', '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_133])).
% 3.38/1.79  tff(c_147, plain, (v1_partfun1('#skF_4', '#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_140])).
% 3.38/1.79  tff(c_149, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_103, c_147])).
% 3.38/1.79  tff(c_150, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_93])).
% 3.38/1.79  tff(c_161, plain, (![C_122, B_123, A_124]: (m1_subset_1(k1_funct_1(C_122, B_123), A_124) | ~r2_hidden(B_123, k1_relat_1(C_122)) | ~v1_funct_1(C_122) | ~v5_relat_1(C_122, A_124) | ~v1_relat_1(C_122))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.38/1.79  tff(c_163, plain, (![B_123, A_124]: (m1_subset_1(k1_funct_1('#skF_4', B_123), A_124) | ~r2_hidden(B_123, '#skF_2') | ~v1_funct_1('#skF_4') | ~v5_relat_1('#skF_4', A_124) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_150, c_161])).
% 3.38/1.79  tff(c_170, plain, (![B_123, A_124]: (m1_subset_1(k1_funct_1('#skF_4', B_123), A_124) | ~r2_hidden(B_123, '#skF_2') | ~v5_relat_1('#skF_4', A_124))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_42, c_163])).
% 3.38/1.79  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_155])).
% 3.38/1.79  tff(c_79, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_71])).
% 3.38/1.79  tff(c_54, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_34, c_48])).
% 3.38/1.79  tff(c_60, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_54])).
% 3.38/1.79  tff(c_36, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_155])).
% 3.38/1.79  tff(c_30, plain, (v1_partfun1('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_155])).
% 3.38/1.79  tff(c_70, plain, (v4_relat_1('#skF_5', '#skF_1')), inference(resolution, [status(thm)], [c_34, c_62])).
% 3.38/1.79  tff(c_84, plain, (k1_relat_1('#skF_5')='#skF_1' | ~v1_partfun1('#skF_5', '#skF_1') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_70, c_81])).
% 3.38/1.79  tff(c_90, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_30, c_84])).
% 3.38/1.79  tff(c_239, plain, (![A_146, B_147, C_148]: (k7_partfun1(A_146, B_147, C_148)=k1_funct_1(B_147, C_148) | ~r2_hidden(C_148, k1_relat_1(B_147)) | ~v1_funct_1(B_147) | ~v5_relat_1(B_147, A_146) | ~v1_relat_1(B_147))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.38/1.79  tff(c_243, plain, (![A_146, C_148]: (k7_partfun1(A_146, '#skF_5', C_148)=k1_funct_1('#skF_5', C_148) | ~r2_hidden(C_148, '#skF_1') | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', A_146) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_90, c_239])).
% 3.38/1.79  tff(c_252, plain, (![A_149, C_150]: (k7_partfun1(A_149, '#skF_5', C_150)=k1_funct_1('#skF_5', C_150) | ~r2_hidden(C_150, '#skF_1') | ~v5_relat_1('#skF_5', A_149))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_36, c_243])).
% 3.38/1.79  tff(c_255, plain, (![A_149, A_1]: (k7_partfun1(A_149, '#skF_5', A_1)=k1_funct_1('#skF_5', A_1) | ~v5_relat_1('#skF_5', A_149) | v1_xboole_0('#skF_1') | ~m1_subset_1(A_1, '#skF_1'))), inference(resolution, [status(thm)], [c_2, c_252])).
% 3.38/1.79  tff(c_266, plain, (![A_153, A_154]: (k7_partfun1(A_153, '#skF_5', A_154)=k1_funct_1('#skF_5', A_154) | ~v5_relat_1('#skF_5', A_153) | ~m1_subset_1(A_154, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_46, c_255])).
% 3.38/1.79  tff(c_270, plain, (![A_155]: (k7_partfun1('#skF_3', '#skF_5', A_155)=k1_funct_1('#skF_5', A_155) | ~m1_subset_1(A_155, '#skF_1'))), inference(resolution, [status(thm)], [c_79, c_266])).
% 3.38/1.79  tff(c_278, plain, (![B_123]: (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', B_123))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', B_123)) | ~r2_hidden(B_123, '#skF_2') | ~v5_relat_1('#skF_4', '#skF_1'))), inference(resolution, [status(thm)], [c_170, c_270])).
% 3.38/1.79  tff(c_282, plain, (![B_123]: (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', B_123))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', B_123)) | ~r2_hidden(B_123, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_278])).
% 3.38/1.79  tff(c_302, plain, (![A_159, B_160, C_161, D_162]: (k3_funct_2(A_159, B_160, C_161, D_162)=k1_funct_1(C_161, D_162) | ~m1_subset_1(D_162, A_159) | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(A_159, B_160))) | ~v1_funct_2(C_161, A_159, B_160) | ~v1_funct_1(C_161) | v1_xboole_0(A_159))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.38/1.79  tff(c_312, plain, (![B_160, C_161]: (k3_funct_2('#skF_2', B_160, C_161, '#skF_6')=k1_funct_1(C_161, '#skF_6') | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_160))) | ~v1_funct_2(C_161, '#skF_2', B_160) | ~v1_funct_1(C_161) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_302])).
% 3.38/1.79  tff(c_334, plain, (![B_164, C_165]: (k3_funct_2('#skF_2', B_164, C_165, '#skF_6')=k1_funct_1(C_165, '#skF_6') | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_164))) | ~v1_funct_2(C_165, '#skF_2', B_164) | ~v1_funct_1(C_165))), inference(negUnitSimplification, [status(thm)], [c_44, c_312])).
% 3.38/1.79  tff(c_345, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_334])).
% 3.38/1.79  tff(c_350, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_345])).
% 3.38/1.79  tff(c_357, plain, (![D_170, C_166, B_167, F_168, A_169, E_171]: (k3_funct_2(B_167, C_166, k8_funct_2(B_167, A_169, C_166, D_170, E_171), F_168)=k1_funct_1(E_171, k3_funct_2(B_167, A_169, D_170, F_168)) | ~v1_partfun1(E_171, A_169) | ~m1_subset_1(F_168, B_167) | ~m1_subset_1(E_171, k1_zfmisc_1(k2_zfmisc_1(A_169, C_166))) | ~v1_funct_1(E_171) | ~m1_subset_1(D_170, k1_zfmisc_1(k2_zfmisc_1(B_167, A_169))) | ~v1_funct_2(D_170, B_167, A_169) | ~v1_funct_1(D_170) | v1_xboole_0(B_167) | v1_xboole_0(A_169))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.38/1.79  tff(c_367, plain, (![B_167, D_170, F_168]: (k3_funct_2(B_167, '#skF_3', k8_funct_2(B_167, '#skF_1', '#skF_3', D_170, '#skF_5'), F_168)=k1_funct_1('#skF_5', k3_funct_2(B_167, '#skF_1', D_170, F_168)) | ~v1_partfun1('#skF_5', '#skF_1') | ~m1_subset_1(F_168, B_167) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_170, k1_zfmisc_1(k2_zfmisc_1(B_167, '#skF_1'))) | ~v1_funct_2(D_170, B_167, '#skF_1') | ~v1_funct_1(D_170) | v1_xboole_0(B_167) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_34, c_357])).
% 3.38/1.79  tff(c_376, plain, (![B_167, D_170, F_168]: (k3_funct_2(B_167, '#skF_3', k8_funct_2(B_167, '#skF_1', '#skF_3', D_170, '#skF_5'), F_168)=k1_funct_1('#skF_5', k3_funct_2(B_167, '#skF_1', D_170, F_168)) | ~m1_subset_1(F_168, B_167) | ~m1_subset_1(D_170, k1_zfmisc_1(k2_zfmisc_1(B_167, '#skF_1'))) | ~v1_funct_2(D_170, B_167, '#skF_1') | ~v1_funct_1(D_170) | v1_xboole_0(B_167) | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_30, c_367])).
% 3.38/1.79  tff(c_439, plain, (![B_189, D_190, F_191]: (k3_funct_2(B_189, '#skF_3', k8_funct_2(B_189, '#skF_1', '#skF_3', D_190, '#skF_5'), F_191)=k1_funct_1('#skF_5', k3_funct_2(B_189, '#skF_1', D_190, F_191)) | ~m1_subset_1(F_191, B_189) | ~m1_subset_1(D_190, k1_zfmisc_1(k2_zfmisc_1(B_189, '#skF_1'))) | ~v1_funct_2(D_190, B_189, '#skF_1') | ~v1_funct_1(D_190) | v1_xboole_0(B_189))), inference(negUnitSimplification, [status(thm)], [c_46, c_376])).
% 3.38/1.79  tff(c_450, plain, (![F_191]: (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_191)=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', F_191)) | ~m1_subset_1(F_191, '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_439])).
% 3.38/1.79  tff(c_456, plain, (![F_191]: (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_191)=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', F_191)) | ~m1_subset_1(F_191, '#skF_2') | v1_xboole_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_450])).
% 3.38/1.79  tff(c_458, plain, (![F_192]: (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_192)=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', F_192)) | ~m1_subset_1(F_192, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_44, c_456])).
% 3.38/1.79  tff(c_28, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k7_partfun1('#skF_3', '#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_155])).
% 3.38/1.79  tff(c_351, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_350, c_28])).
% 3.38/1.79  tff(c_464, plain, (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))!=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')) | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_458, c_351])).
% 3.38/1.79  tff(c_470, plain, (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_350, c_464])).
% 3.38/1.79  tff(c_475, plain, (~r2_hidden('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_282, c_470])).
% 3.38/1.79  tff(c_478, plain, (v1_xboole_0('#skF_2') | ~m1_subset_1('#skF_6', '#skF_2')), inference(resolution, [status(thm)], [c_2, c_475])).
% 3.38/1.79  tff(c_481, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_478])).
% 3.38/1.79  tff(c_483, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_481])).
% 3.38/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.38/1.79  
% 3.38/1.79  Inference rules
% 3.38/1.79  ----------------------
% 3.38/1.79  #Ref     : 0
% 3.38/1.79  #Sup     : 85
% 3.38/1.79  #Fact    : 0
% 3.38/1.79  #Define  : 0
% 3.38/1.79  #Split   : 8
% 3.38/1.79  #Chain   : 0
% 3.38/1.79  #Close   : 0
% 3.38/1.79  
% 3.38/1.79  Ordering : KBO
% 3.38/1.79  
% 3.38/1.79  Simplification rules
% 3.38/1.79  ----------------------
% 3.38/1.79  #Subsume      : 2
% 3.38/1.79  #Demod        : 51
% 3.38/1.79  #Tautology    : 17
% 3.38/1.79  #SimpNegUnit  : 11
% 3.38/1.79  #BackRed      : 1
% 3.38/1.79  
% 3.38/1.79  #Partial instantiations: 0
% 3.38/1.79  #Strategies tried      : 1
% 3.38/1.79  
% 3.38/1.79  Timing (in seconds)
% 3.38/1.79  ----------------------
% 3.38/1.79  Preprocessing        : 0.56
% 3.38/1.79  Parsing              : 0.28
% 3.38/1.79  CNF conversion       : 0.06
% 3.38/1.79  Main loop            : 0.29
% 3.38/1.79  Inferencing          : 0.10
% 3.38/1.79  Reduction            : 0.09
% 3.38/1.79  Demodulation         : 0.06
% 3.38/1.79  BG Simplification    : 0.03
% 3.38/1.79  Subsumption          : 0.05
% 3.38/1.79  Abstraction          : 0.02
% 3.38/1.79  MUC search           : 0.00
% 3.38/1.79  Cooper               : 0.00
% 3.38/1.79  Total                : 0.88
% 3.38/1.79  Index Insertion      : 0.00
% 3.38/1.79  Index Deletion       : 0.00
% 3.38/1.79  Index Matching       : 0.00
% 3.38/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
