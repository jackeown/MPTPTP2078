%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:08 EST 2020

% Result     : Theorem 4.44s
% Output     : CNFRefutation 4.56s
% Verified   : 
% Statistics : Number of formulae       :  117 (1009 expanded)
%              Number of leaves         :   40 ( 369 expanded)
%              Depth                    :   24
%              Number of atoms          :  225 (3558 expanded)
%              Number of equality atoms :   37 ( 734 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_152,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ v1_xboole_0(B)
       => ! [C] :
            ( ~ v1_xboole_0(C)
           => ! [D] :
                ( ( v1_funct_1(D)
                  & v1_funct_2(D,B,C)
                  & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
               => ( ! [E] :
                      ( m1_subset_1(E,B)
                     => r2_hidden(k3_funct_2(B,C,D,E),A) )
                 => r1_tarski(k2_relset_1(B,C,D),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_funct_2)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_100,axiom,(
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

tff(f_130,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( k1_relat_1(C) = A
          & ! [D] :
              ( r2_hidden(D,A)
             => r2_hidden(k1_funct_1(C,D),B) ) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_113,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_45,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_66,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(c_64,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_58,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_225,plain,(
    ! [A_94,B_95,C_96] :
      ( k2_relset_1(A_94,B_95,C_96) = k2_relat_1(C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_244,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_225])).

tff(c_54,plain,(
    ~ r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_245,plain,(
    ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_54])).

tff(c_62,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_60,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_66,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_99,plain,(
    ! [C_64,A_65,B_66] :
      ( v1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_108,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_99])).

tff(c_311,plain,(
    ! [A_111,B_112,C_113] :
      ( k1_relset_1(A_111,B_112,C_113) = k1_relat_1(C_113)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_330,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_311])).

tff(c_688,plain,(
    ! [B_146,A_147,C_148] :
      ( k1_xboole_0 = B_146
      | k1_relset_1(A_147,B_146,C_148) = A_147
      | ~ v1_funct_2(C_148,A_147,B_146)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(A_147,B_146))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_715,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_688])).

tff(c_725,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_330,c_715])).

tff(c_726,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_725])).

tff(c_823,plain,(
    ! [C_155,B_156] :
      ( r2_hidden('#skF_2'(k1_relat_1(C_155),B_156,C_155),k1_relat_1(C_155))
      | v1_funct_2(C_155,k1_relat_1(C_155),B_156)
      | ~ v1_funct_1(C_155)
      | ~ v1_relat_1(C_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_832,plain,(
    ! [B_156] :
      ( r2_hidden('#skF_2'('#skF_4',B_156,'#skF_6'),k1_relat_1('#skF_6'))
      | v1_funct_2('#skF_6',k1_relat_1('#skF_6'),B_156)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_726,c_823])).

tff(c_880,plain,(
    ! [B_164] :
      ( r2_hidden('#skF_2'('#skF_4',B_164,'#skF_6'),'#skF_4')
      | v1_funct_2('#skF_6','#skF_4',B_164) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_62,c_726,c_726,c_832])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_888,plain,(
    ! [B_164] :
      ( m1_subset_1('#skF_2'('#skF_4',B_164,'#skF_6'),'#skF_4')
      | v1_funct_2('#skF_6','#skF_4',B_164) ) ),
    inference(resolution,[status(thm)],[c_880,c_12])).

tff(c_1144,plain,(
    ! [A_189,B_190,C_191,D_192] :
      ( k3_funct_2(A_189,B_190,C_191,D_192) = k1_funct_1(C_191,D_192)
      | ~ m1_subset_1(D_192,A_189)
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(A_189,B_190)))
      | ~ v1_funct_2(C_191,A_189,B_190)
      | ~ v1_funct_1(C_191)
      | v1_xboole_0(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1152,plain,(
    ! [B_190,C_191,B_164] :
      ( k3_funct_2('#skF_4',B_190,C_191,'#skF_2'('#skF_4',B_164,'#skF_6')) = k1_funct_1(C_191,'#skF_2'('#skF_4',B_164,'#skF_6'))
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_190)))
      | ~ v1_funct_2(C_191,'#skF_4',B_190)
      | ~ v1_funct_1(C_191)
      | v1_xboole_0('#skF_4')
      | v1_funct_2('#skF_6','#skF_4',B_164) ) ),
    inference(resolution,[status(thm)],[c_888,c_1144])).

tff(c_1186,plain,(
    ! [B_193,C_194,B_195] :
      ( k3_funct_2('#skF_4',B_193,C_194,'#skF_2'('#skF_4',B_195,'#skF_6')) = k1_funct_1(C_194,'#skF_2'('#skF_4',B_195,'#skF_6'))
      | ~ m1_subset_1(C_194,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_193)))
      | ~ v1_funct_2(C_194,'#skF_4',B_193)
      | ~ v1_funct_1(C_194)
      | v1_funct_2('#skF_6','#skF_4',B_195) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1152])).

tff(c_1205,plain,(
    ! [B_195] :
      ( k3_funct_2('#skF_4','#skF_5','#skF_6','#skF_2'('#skF_4',B_195,'#skF_6')) = k1_funct_1('#skF_6','#skF_2'('#skF_4',B_195,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6')
      | v1_funct_2('#skF_6','#skF_4',B_195) ) ),
    inference(resolution,[status(thm)],[c_58,c_1186])).

tff(c_1840,plain,(
    ! [B_244] :
      ( k3_funct_2('#skF_4','#skF_5','#skF_6','#skF_2'('#skF_4',B_244,'#skF_6')) = k1_funct_1('#skF_6','#skF_2'('#skF_4',B_244,'#skF_6'))
      | v1_funct_2('#skF_6','#skF_4',B_244) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1205])).

tff(c_56,plain,(
    ! [E_49] :
      ( r2_hidden(k3_funct_2('#skF_4','#skF_5','#skF_6',E_49),'#skF_3')
      | ~ m1_subset_1(E_49,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_1930,plain,(
    ! [B_252] :
      ( r2_hidden(k1_funct_1('#skF_6','#skF_2'('#skF_4',B_252,'#skF_6')),'#skF_3')
      | ~ m1_subset_1('#skF_2'('#skF_4',B_252,'#skF_6'),'#skF_4')
      | v1_funct_2('#skF_6','#skF_4',B_252) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1840,c_56])).

tff(c_891,plain,(
    ! [C_167,B_168] :
      ( ~ r2_hidden(k1_funct_1(C_167,'#skF_2'(k1_relat_1(C_167),B_168,C_167)),B_168)
      | v1_funct_2(C_167,k1_relat_1(C_167),B_168)
      | ~ v1_funct_1(C_167)
      | ~ v1_relat_1(C_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_894,plain,(
    ! [B_168] :
      ( ~ r2_hidden(k1_funct_1('#skF_6','#skF_2'('#skF_4',B_168,'#skF_6')),B_168)
      | v1_funct_2('#skF_6',k1_relat_1('#skF_6'),B_168)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_726,c_891])).

tff(c_896,plain,(
    ! [B_168] :
      ( ~ r2_hidden(k1_funct_1('#skF_6','#skF_2'('#skF_4',B_168,'#skF_6')),B_168)
      | v1_funct_2('#skF_6','#skF_4',B_168) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_62,c_726,c_894])).

tff(c_1946,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_4','#skF_3','#skF_6'),'#skF_4')
    | v1_funct_2('#skF_6','#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_1930,c_896])).

tff(c_1949,plain,(
    ~ m1_subset_1('#skF_2'('#skF_4','#skF_3','#skF_6'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1946])).

tff(c_1006,plain,(
    ! [C_173,B_174] :
      ( r2_hidden('#skF_2'(k1_relat_1(C_173),B_174,C_173),k1_relat_1(C_173))
      | m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_173),B_174)))
      | ~ v1_funct_1(C_173)
      | ~ v1_relat_1(C_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1015,plain,(
    ! [B_174] :
      ( r2_hidden('#skF_2'('#skF_4',B_174,'#skF_6'),k1_relat_1('#skF_6'))
      | m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),B_174)))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_726,c_1006])).

tff(c_1040,plain,(
    ! [B_178] :
      ( r2_hidden('#skF_2'('#skF_4',B_178,'#skF_6'),'#skF_4')
      | m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_178))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_62,c_726,c_726,c_1015])).

tff(c_26,plain,(
    ! [A_24,B_25,C_26] :
      ( k2_relset_1(A_24,B_25,C_26) = k2_relat_1(C_26)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1390,plain,(
    ! [B_208] :
      ( k2_relset_1('#skF_4',B_208,'#skF_6') = k2_relat_1('#skF_6')
      | r2_hidden('#skF_2'('#skF_4',B_208,'#skF_6'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1040,c_26])).

tff(c_1398,plain,(
    ! [B_208] :
      ( m1_subset_1('#skF_2'('#skF_4',B_208,'#skF_6'),'#skF_4')
      | k2_relset_1('#skF_4',B_208,'#skF_6') = k2_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1390,c_12])).

tff(c_1959,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1398,c_1949])).

tff(c_1022,plain,(
    ! [B_174] :
      ( r2_hidden('#skF_2'('#skF_4',B_174,'#skF_6'),'#skF_4')
      | m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_174))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_62,c_726,c_726,c_1015])).

tff(c_335,plain,(
    ! [A_114,B_115,C_116] :
      ( m1_subset_1(k2_relset_1(A_114,B_115,C_116),k1_zfmisc_1(B_115))
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1221,plain,(
    ! [A_196,B_197,C_198] :
      ( r1_tarski(k2_relset_1(A_196,B_197,C_198),B_197)
      | ~ m1_subset_1(C_198,k1_zfmisc_1(k2_zfmisc_1(A_196,B_197))) ) ),
    inference(resolution,[status(thm)],[c_335,c_14])).

tff(c_1399,plain,(
    ! [B_209] :
      ( r1_tarski(k2_relset_1('#skF_4',B_209,'#skF_6'),B_209)
      | r2_hidden('#skF_2'('#skF_4',B_209,'#skF_6'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1022,c_1221])).

tff(c_1435,plain,(
    ! [B_209] :
      ( m1_subset_1('#skF_2'('#skF_4',B_209,'#skF_6'),'#skF_4')
      | r1_tarski(k2_relset_1('#skF_4',B_209,'#skF_6'),B_209) ) ),
    inference(resolution,[status(thm)],[c_1399,c_12])).

tff(c_1972,plain,
    ( m1_subset_1('#skF_2'('#skF_4','#skF_3','#skF_6'),'#skF_4')
    | r1_tarski(k2_relat_1('#skF_6'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1959,c_1435])).

tff(c_1984,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_245,c_1949,c_1972])).

tff(c_1986,plain,(
    m1_subset_1('#skF_2'('#skF_4','#skF_3','#skF_6'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_1946])).

tff(c_40,plain,(
    ! [A_30,B_31,C_32,D_33] :
      ( k3_funct_2(A_30,B_31,C_32,D_33) = k1_funct_1(C_32,D_33)
      | ~ m1_subset_1(D_33,A_30)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31)))
      | ~ v1_funct_2(C_32,A_30,B_31)
      | ~ v1_funct_1(C_32)
      | v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2002,plain,(
    ! [B_31,C_32] :
      ( k3_funct_2('#skF_4',B_31,C_32,'#skF_2'('#skF_4','#skF_3','#skF_6')) = k1_funct_1(C_32,'#skF_2'('#skF_4','#skF_3','#skF_6'))
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_31)))
      | ~ v1_funct_2(C_32,'#skF_4',B_31)
      | ~ v1_funct_1(C_32)
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1986,c_40])).

tff(c_2007,plain,(
    ! [B_255,C_256] :
      ( k3_funct_2('#skF_4',B_255,C_256,'#skF_2'('#skF_4','#skF_3','#skF_6')) = k1_funct_1(C_256,'#skF_2'('#skF_4','#skF_3','#skF_6'))
      | ~ m1_subset_1(C_256,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_255)))
      | ~ v1_funct_2(C_256,'#skF_4',B_255)
      | ~ v1_funct_1(C_256) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_2002])).

tff(c_2033,plain,
    ( k3_funct_2('#skF_4','#skF_5','#skF_6','#skF_2'('#skF_4','#skF_3','#skF_6')) = k1_funct_1('#skF_6','#skF_2'('#skF_4','#skF_3','#skF_6'))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_2007])).

tff(c_2044,plain,(
    k3_funct_2('#skF_4','#skF_5','#skF_6','#skF_2'('#skF_4','#skF_3','#skF_6')) = k1_funct_1('#skF_6','#skF_2'('#skF_4','#skF_3','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_2033])).

tff(c_2060,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_2'('#skF_4','#skF_3','#skF_6')),'#skF_3')
    | ~ m1_subset_1('#skF_2'('#skF_4','#skF_3','#skF_6'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2044,c_56])).

tff(c_2075,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_2'('#skF_4','#skF_3','#skF_6')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1986,c_2060])).

tff(c_1086,plain,(
    ! [C_181,B_182] :
      ( ~ r2_hidden(k1_funct_1(C_181,'#skF_2'(k1_relat_1(C_181),B_182,C_181)),B_182)
      | m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_181),B_182)))
      | ~ v1_funct_1(C_181)
      | ~ v1_relat_1(C_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1089,plain,(
    ! [B_182] :
      ( ~ r2_hidden(k1_funct_1('#skF_6','#skF_2'('#skF_4',B_182,'#skF_6')),B_182)
      | m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),B_182)))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_726,c_1086])).

tff(c_1091,plain,(
    ! [B_182] :
      ( ~ r2_hidden(k1_funct_1('#skF_6','#skF_2'('#skF_4',B_182,'#skF_6')),B_182)
      | m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_182))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_62,c_726,c_1089])).

tff(c_2094,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_2075,c_1091])).

tff(c_2169,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2094,c_26])).

tff(c_360,plain,(
    ! [A_114,B_115,C_116] :
      ( r1_tarski(k2_relset_1(A_114,B_115,C_116),B_115)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(resolution,[status(thm)],[c_335,c_14])).

tff(c_2157,plain,(
    r1_tarski(k2_relset_1('#skF_4','#skF_3','#skF_6'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_2094,c_360])).

tff(c_2239,plain,(
    r1_tarski(k2_relat_1('#skF_6'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2169,c_2157])).

tff(c_2241,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_245,c_2239])).

tff(c_2242,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_725])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_90,plain,(
    ! [A_62,B_63] :
      ( r2_hidden('#skF_1'(A_62,B_63),A_62)
      | r1_xboole_0(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    ! [B_14,A_13] :
      ( ~ r1_tarski(B_14,A_13)
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_141,plain,(
    ! [A_75,B_76] :
      ( ~ r1_tarski(A_75,'#skF_1'(A_75,B_76))
      | r1_xboole_0(A_75,B_76) ) ),
    inference(resolution,[status(thm)],[c_90,c_18])).

tff(c_147,plain,(
    ! [B_77] : r1_xboole_0(k1_xboole_0,B_77) ),
    inference(resolution,[status(thm)],[c_8,c_141])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( ~ r1_xboole_0(B_8,A_7)
      | ~ r1_tarski(B_8,A_7)
      | v1_xboole_0(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_150,plain,(
    ! [B_77] :
      ( ~ r1_tarski(k1_xboole_0,B_77)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_147,c_10])).

tff(c_153,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_150])).

tff(c_2273,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2242,c_153])).

tff(c_2278,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2273])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:27:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.44/1.78  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.56/1.79  
% 4.56/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.56/1.79  %$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 4.56/1.79  
% 4.56/1.79  %Foreground sorts:
% 4.56/1.79  
% 4.56/1.79  
% 4.56/1.79  %Background operators:
% 4.56/1.79  
% 4.56/1.79  
% 4.56/1.79  %Foreground operators:
% 4.56/1.79  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.56/1.79  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.56/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.56/1.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.56/1.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.56/1.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.56/1.79  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.56/1.79  tff('#skF_5', type, '#skF_5': $i).
% 4.56/1.79  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.56/1.79  tff('#skF_6', type, '#skF_6': $i).
% 4.56/1.79  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.56/1.79  tff('#skF_3', type, '#skF_3': $i).
% 4.56/1.79  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.56/1.79  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.56/1.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.56/1.79  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.56/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.56/1.79  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.56/1.79  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.56/1.79  tff('#skF_4', type, '#skF_4': $i).
% 4.56/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.56/1.79  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.56/1.79  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.56/1.79  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 4.56/1.79  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.56/1.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.56/1.79  
% 4.56/1.81  tff(f_152, negated_conjecture, ~(![A, B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((![E]: (m1_subset_1(E, B) => r2_hidden(k3_funct_2(B, C, D, E), A))) => r1_tarski(k2_relset_1(B, C, D), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t191_funct_2)).
% 4.56/1.81  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.56/1.81  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.56/1.81  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.56/1.81  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.56/1.81  tff(f_130, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(C) = A) & (![D]: (r2_hidden(D, A) => r2_hidden(k1_funct_1(C, D), B)))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_funct_2)).
% 4.56/1.81  tff(f_57, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 4.56/1.81  tff(f_113, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 4.56/1.81  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 4.56/1.81  tff(f_61, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.56/1.81  tff(f_45, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.56/1.81  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.56/1.81  tff(f_66, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.56/1.81  tff(f_53, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 4.56/1.81  tff(c_64, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.56/1.81  tff(c_58, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.56/1.81  tff(c_225, plain, (![A_94, B_95, C_96]: (k2_relset_1(A_94, B_95, C_96)=k2_relat_1(C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.56/1.81  tff(c_244, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_58, c_225])).
% 4.56/1.81  tff(c_54, plain, (~r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.56/1.81  tff(c_245, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_244, c_54])).
% 4.56/1.81  tff(c_62, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.56/1.81  tff(c_60, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.56/1.81  tff(c_66, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.56/1.81  tff(c_99, plain, (![C_64, A_65, B_66]: (v1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.56/1.81  tff(c_108, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_58, c_99])).
% 4.56/1.81  tff(c_311, plain, (![A_111, B_112, C_113]: (k1_relset_1(A_111, B_112, C_113)=k1_relat_1(C_113) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.56/1.81  tff(c_330, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_58, c_311])).
% 4.56/1.81  tff(c_688, plain, (![B_146, A_147, C_148]: (k1_xboole_0=B_146 | k1_relset_1(A_147, B_146, C_148)=A_147 | ~v1_funct_2(C_148, A_147, B_146) | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1(A_147, B_146))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.56/1.81  tff(c_715, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_58, c_688])).
% 4.56/1.81  tff(c_725, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_330, c_715])).
% 4.56/1.81  tff(c_726, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_725])).
% 4.56/1.81  tff(c_823, plain, (![C_155, B_156]: (r2_hidden('#skF_2'(k1_relat_1(C_155), B_156, C_155), k1_relat_1(C_155)) | v1_funct_2(C_155, k1_relat_1(C_155), B_156) | ~v1_funct_1(C_155) | ~v1_relat_1(C_155))), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.56/1.81  tff(c_832, plain, (![B_156]: (r2_hidden('#skF_2'('#skF_4', B_156, '#skF_6'), k1_relat_1('#skF_6')) | v1_funct_2('#skF_6', k1_relat_1('#skF_6'), B_156) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_726, c_823])).
% 4.56/1.81  tff(c_880, plain, (![B_164]: (r2_hidden('#skF_2'('#skF_4', B_164, '#skF_6'), '#skF_4') | v1_funct_2('#skF_6', '#skF_4', B_164))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_62, c_726, c_726, c_832])).
% 4.56/1.81  tff(c_12, plain, (![A_9, B_10]: (m1_subset_1(A_9, B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.56/1.81  tff(c_888, plain, (![B_164]: (m1_subset_1('#skF_2'('#skF_4', B_164, '#skF_6'), '#skF_4') | v1_funct_2('#skF_6', '#skF_4', B_164))), inference(resolution, [status(thm)], [c_880, c_12])).
% 4.56/1.81  tff(c_1144, plain, (![A_189, B_190, C_191, D_192]: (k3_funct_2(A_189, B_190, C_191, D_192)=k1_funct_1(C_191, D_192) | ~m1_subset_1(D_192, A_189) | ~m1_subset_1(C_191, k1_zfmisc_1(k2_zfmisc_1(A_189, B_190))) | ~v1_funct_2(C_191, A_189, B_190) | ~v1_funct_1(C_191) | v1_xboole_0(A_189))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.56/1.81  tff(c_1152, plain, (![B_190, C_191, B_164]: (k3_funct_2('#skF_4', B_190, C_191, '#skF_2'('#skF_4', B_164, '#skF_6'))=k1_funct_1(C_191, '#skF_2'('#skF_4', B_164, '#skF_6')) | ~m1_subset_1(C_191, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_190))) | ~v1_funct_2(C_191, '#skF_4', B_190) | ~v1_funct_1(C_191) | v1_xboole_0('#skF_4') | v1_funct_2('#skF_6', '#skF_4', B_164))), inference(resolution, [status(thm)], [c_888, c_1144])).
% 4.56/1.81  tff(c_1186, plain, (![B_193, C_194, B_195]: (k3_funct_2('#skF_4', B_193, C_194, '#skF_2'('#skF_4', B_195, '#skF_6'))=k1_funct_1(C_194, '#skF_2'('#skF_4', B_195, '#skF_6')) | ~m1_subset_1(C_194, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_193))) | ~v1_funct_2(C_194, '#skF_4', B_193) | ~v1_funct_1(C_194) | v1_funct_2('#skF_6', '#skF_4', B_195))), inference(negUnitSimplification, [status(thm)], [c_66, c_1152])).
% 4.56/1.81  tff(c_1205, plain, (![B_195]: (k3_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_2'('#skF_4', B_195, '#skF_6'))=k1_funct_1('#skF_6', '#skF_2'('#skF_4', B_195, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | v1_funct_2('#skF_6', '#skF_4', B_195))), inference(resolution, [status(thm)], [c_58, c_1186])).
% 4.56/1.81  tff(c_1840, plain, (![B_244]: (k3_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_2'('#skF_4', B_244, '#skF_6'))=k1_funct_1('#skF_6', '#skF_2'('#skF_4', B_244, '#skF_6')) | v1_funct_2('#skF_6', '#skF_4', B_244))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_1205])).
% 4.56/1.81  tff(c_56, plain, (![E_49]: (r2_hidden(k3_funct_2('#skF_4', '#skF_5', '#skF_6', E_49), '#skF_3') | ~m1_subset_1(E_49, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.56/1.81  tff(c_1930, plain, (![B_252]: (r2_hidden(k1_funct_1('#skF_6', '#skF_2'('#skF_4', B_252, '#skF_6')), '#skF_3') | ~m1_subset_1('#skF_2'('#skF_4', B_252, '#skF_6'), '#skF_4') | v1_funct_2('#skF_6', '#skF_4', B_252))), inference(superposition, [status(thm), theory('equality')], [c_1840, c_56])).
% 4.56/1.81  tff(c_891, plain, (![C_167, B_168]: (~r2_hidden(k1_funct_1(C_167, '#skF_2'(k1_relat_1(C_167), B_168, C_167)), B_168) | v1_funct_2(C_167, k1_relat_1(C_167), B_168) | ~v1_funct_1(C_167) | ~v1_relat_1(C_167))), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.56/1.81  tff(c_894, plain, (![B_168]: (~r2_hidden(k1_funct_1('#skF_6', '#skF_2'('#skF_4', B_168, '#skF_6')), B_168) | v1_funct_2('#skF_6', k1_relat_1('#skF_6'), B_168) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_726, c_891])).
% 4.56/1.81  tff(c_896, plain, (![B_168]: (~r2_hidden(k1_funct_1('#skF_6', '#skF_2'('#skF_4', B_168, '#skF_6')), B_168) | v1_funct_2('#skF_6', '#skF_4', B_168))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_62, c_726, c_894])).
% 4.56/1.81  tff(c_1946, plain, (~m1_subset_1('#skF_2'('#skF_4', '#skF_3', '#skF_6'), '#skF_4') | v1_funct_2('#skF_6', '#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_1930, c_896])).
% 4.56/1.81  tff(c_1949, plain, (~m1_subset_1('#skF_2'('#skF_4', '#skF_3', '#skF_6'), '#skF_4')), inference(splitLeft, [status(thm)], [c_1946])).
% 4.56/1.81  tff(c_1006, plain, (![C_173, B_174]: (r2_hidden('#skF_2'(k1_relat_1(C_173), B_174, C_173), k1_relat_1(C_173)) | m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_173), B_174))) | ~v1_funct_1(C_173) | ~v1_relat_1(C_173))), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.56/1.81  tff(c_1015, plain, (![B_174]: (r2_hidden('#skF_2'('#skF_4', B_174, '#skF_6'), k1_relat_1('#skF_6')) | m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), B_174))) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_726, c_1006])).
% 4.56/1.81  tff(c_1040, plain, (![B_178]: (r2_hidden('#skF_2'('#skF_4', B_178, '#skF_6'), '#skF_4') | m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_178))))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_62, c_726, c_726, c_1015])).
% 4.56/1.81  tff(c_26, plain, (![A_24, B_25, C_26]: (k2_relset_1(A_24, B_25, C_26)=k2_relat_1(C_26) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.56/1.81  tff(c_1390, plain, (![B_208]: (k2_relset_1('#skF_4', B_208, '#skF_6')=k2_relat_1('#skF_6') | r2_hidden('#skF_2'('#skF_4', B_208, '#skF_6'), '#skF_4'))), inference(resolution, [status(thm)], [c_1040, c_26])).
% 4.56/1.81  tff(c_1398, plain, (![B_208]: (m1_subset_1('#skF_2'('#skF_4', B_208, '#skF_6'), '#skF_4') | k2_relset_1('#skF_4', B_208, '#skF_6')=k2_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_1390, c_12])).
% 4.56/1.81  tff(c_1959, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_1398, c_1949])).
% 4.56/1.81  tff(c_1022, plain, (![B_174]: (r2_hidden('#skF_2'('#skF_4', B_174, '#skF_6'), '#skF_4') | m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_174))))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_62, c_726, c_726, c_1015])).
% 4.56/1.81  tff(c_335, plain, (![A_114, B_115, C_116]: (m1_subset_1(k2_relset_1(A_114, B_115, C_116), k1_zfmisc_1(B_115)) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.56/1.81  tff(c_14, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~m1_subset_1(A_11, k1_zfmisc_1(B_12)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.56/1.81  tff(c_1221, plain, (![A_196, B_197, C_198]: (r1_tarski(k2_relset_1(A_196, B_197, C_198), B_197) | ~m1_subset_1(C_198, k1_zfmisc_1(k2_zfmisc_1(A_196, B_197))))), inference(resolution, [status(thm)], [c_335, c_14])).
% 4.56/1.81  tff(c_1399, plain, (![B_209]: (r1_tarski(k2_relset_1('#skF_4', B_209, '#skF_6'), B_209) | r2_hidden('#skF_2'('#skF_4', B_209, '#skF_6'), '#skF_4'))), inference(resolution, [status(thm)], [c_1022, c_1221])).
% 4.56/1.81  tff(c_1435, plain, (![B_209]: (m1_subset_1('#skF_2'('#skF_4', B_209, '#skF_6'), '#skF_4') | r1_tarski(k2_relset_1('#skF_4', B_209, '#skF_6'), B_209))), inference(resolution, [status(thm)], [c_1399, c_12])).
% 4.56/1.81  tff(c_1972, plain, (m1_subset_1('#skF_2'('#skF_4', '#skF_3', '#skF_6'), '#skF_4') | r1_tarski(k2_relat_1('#skF_6'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1959, c_1435])).
% 4.56/1.81  tff(c_1984, plain, $false, inference(negUnitSimplification, [status(thm)], [c_245, c_1949, c_1972])).
% 4.56/1.81  tff(c_1986, plain, (m1_subset_1('#skF_2'('#skF_4', '#skF_3', '#skF_6'), '#skF_4')), inference(splitRight, [status(thm)], [c_1946])).
% 4.56/1.81  tff(c_40, plain, (![A_30, B_31, C_32, D_33]: (k3_funct_2(A_30, B_31, C_32, D_33)=k1_funct_1(C_32, D_33) | ~m1_subset_1(D_33, A_30) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))) | ~v1_funct_2(C_32, A_30, B_31) | ~v1_funct_1(C_32) | v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.56/1.81  tff(c_2002, plain, (![B_31, C_32]: (k3_funct_2('#skF_4', B_31, C_32, '#skF_2'('#skF_4', '#skF_3', '#skF_6'))=k1_funct_1(C_32, '#skF_2'('#skF_4', '#skF_3', '#skF_6')) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_31))) | ~v1_funct_2(C_32, '#skF_4', B_31) | ~v1_funct_1(C_32) | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_1986, c_40])).
% 4.56/1.81  tff(c_2007, plain, (![B_255, C_256]: (k3_funct_2('#skF_4', B_255, C_256, '#skF_2'('#skF_4', '#skF_3', '#skF_6'))=k1_funct_1(C_256, '#skF_2'('#skF_4', '#skF_3', '#skF_6')) | ~m1_subset_1(C_256, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_255))) | ~v1_funct_2(C_256, '#skF_4', B_255) | ~v1_funct_1(C_256))), inference(negUnitSimplification, [status(thm)], [c_66, c_2002])).
% 4.56/1.81  tff(c_2033, plain, (k3_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_2'('#skF_4', '#skF_3', '#skF_6'))=k1_funct_1('#skF_6', '#skF_2'('#skF_4', '#skF_3', '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_58, c_2007])).
% 4.56/1.81  tff(c_2044, plain, (k3_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_2'('#skF_4', '#skF_3', '#skF_6'))=k1_funct_1('#skF_6', '#skF_2'('#skF_4', '#skF_3', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_2033])).
% 4.56/1.81  tff(c_2060, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_2'('#skF_4', '#skF_3', '#skF_6')), '#skF_3') | ~m1_subset_1('#skF_2'('#skF_4', '#skF_3', '#skF_6'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2044, c_56])).
% 4.56/1.81  tff(c_2075, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_2'('#skF_4', '#skF_3', '#skF_6')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1986, c_2060])).
% 4.56/1.81  tff(c_1086, plain, (![C_181, B_182]: (~r2_hidden(k1_funct_1(C_181, '#skF_2'(k1_relat_1(C_181), B_182, C_181)), B_182) | m1_subset_1(C_181, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_181), B_182))) | ~v1_funct_1(C_181) | ~v1_relat_1(C_181))), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.56/1.81  tff(c_1089, plain, (![B_182]: (~r2_hidden(k1_funct_1('#skF_6', '#skF_2'('#skF_4', B_182, '#skF_6')), B_182) | m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), B_182))) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_726, c_1086])).
% 4.56/1.81  tff(c_1091, plain, (![B_182]: (~r2_hidden(k1_funct_1('#skF_6', '#skF_2'('#skF_4', B_182, '#skF_6')), B_182) | m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_182))))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_62, c_726, c_1089])).
% 4.56/1.81  tff(c_2094, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(resolution, [status(thm)], [c_2075, c_1091])).
% 4.56/1.81  tff(c_2169, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2094, c_26])).
% 4.56/1.81  tff(c_360, plain, (![A_114, B_115, C_116]: (r1_tarski(k2_relset_1(A_114, B_115, C_116), B_115) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(resolution, [status(thm)], [c_335, c_14])).
% 4.56/1.81  tff(c_2157, plain, (r1_tarski(k2_relset_1('#skF_4', '#skF_3', '#skF_6'), '#skF_3')), inference(resolution, [status(thm)], [c_2094, c_360])).
% 4.56/1.81  tff(c_2239, plain, (r1_tarski(k2_relat_1('#skF_6'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2169, c_2157])).
% 4.56/1.81  tff(c_2241, plain, $false, inference(negUnitSimplification, [status(thm)], [c_245, c_2239])).
% 4.56/1.81  tff(c_2242, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_725])).
% 4.56/1.81  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.56/1.81  tff(c_90, plain, (![A_62, B_63]: (r2_hidden('#skF_1'(A_62, B_63), A_62) | r1_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.56/1.81  tff(c_18, plain, (![B_14, A_13]: (~r1_tarski(B_14, A_13) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.56/1.81  tff(c_141, plain, (![A_75, B_76]: (~r1_tarski(A_75, '#skF_1'(A_75, B_76)) | r1_xboole_0(A_75, B_76))), inference(resolution, [status(thm)], [c_90, c_18])).
% 4.56/1.81  tff(c_147, plain, (![B_77]: (r1_xboole_0(k1_xboole_0, B_77))), inference(resolution, [status(thm)], [c_8, c_141])).
% 4.56/1.81  tff(c_10, plain, (![B_8, A_7]: (~r1_xboole_0(B_8, A_7) | ~r1_tarski(B_8, A_7) | v1_xboole_0(B_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.56/1.81  tff(c_150, plain, (![B_77]: (~r1_tarski(k1_xboole_0, B_77) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_147, c_10])).
% 4.56/1.81  tff(c_153, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_150])).
% 4.56/1.81  tff(c_2273, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2242, c_153])).
% 4.56/1.81  tff(c_2278, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_2273])).
% 4.56/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.56/1.81  
% 4.56/1.81  Inference rules
% 4.56/1.81  ----------------------
% 4.56/1.81  #Ref     : 0
% 4.56/1.81  #Sup     : 433
% 4.56/1.81  #Fact    : 0
% 4.56/1.81  #Define  : 0
% 4.56/1.81  #Split   : 8
% 4.56/1.81  #Chain   : 0
% 4.56/1.81  #Close   : 0
% 4.56/1.81  
% 4.56/1.81  Ordering : KBO
% 4.56/1.81  
% 4.56/1.81  Simplification rules
% 4.56/1.81  ----------------------
% 4.56/1.81  #Subsume      : 60
% 4.56/1.81  #Demod        : 347
% 4.56/1.81  #Tautology    : 118
% 4.56/1.81  #SimpNegUnit  : 19
% 4.56/1.81  #BackRed      : 58
% 4.56/1.81  
% 4.56/1.81  #Partial instantiations: 0
% 4.56/1.81  #Strategies tried      : 1
% 4.56/1.81  
% 4.56/1.81  Timing (in seconds)
% 4.56/1.81  ----------------------
% 4.56/1.81  Preprocessing        : 0.36
% 4.56/1.81  Parsing              : 0.19
% 4.56/1.81  CNF conversion       : 0.03
% 4.56/1.81  Main loop            : 0.66
% 4.56/1.81  Inferencing          : 0.23
% 4.56/1.81  Reduction            : 0.22
% 4.56/1.81  Demodulation         : 0.16
% 4.56/1.81  BG Simplification    : 0.03
% 4.56/1.81  Subsumption          : 0.11
% 4.56/1.81  Abstraction          : 0.04
% 4.56/1.81  MUC search           : 0.00
% 4.56/1.81  Cooper               : 0.00
% 4.56/1.81  Total                : 1.06
% 4.56/1.81  Index Insertion      : 0.00
% 4.56/1.81  Index Deletion       : 0.00
% 4.56/1.81  Index Matching       : 0.00
% 4.56/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
