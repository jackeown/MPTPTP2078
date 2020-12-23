%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0717+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:45 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   57 (  79 expanded)
%              Number of leaves         :   28 (  41 expanded)
%              Depth                    :    8
%              Number of atoms          :   98 ( 172 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v5_relat_1(B,A)
          & v1_funct_1(B) )
       => ! [C] :
            ( r2_hidden(C,k1_relat_1(B))
           => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(c_40,plain,(
    v5_relat_1('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_42,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_38,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_36,plain,(
    r2_hidden('#skF_7',k1_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k2_relat_1(B_2),A_1)
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_89,plain,(
    ! [A_81,D_82] :
      ( r2_hidden(k1_funct_1(A_81,D_82),k2_relat_1(A_81))
      | ~ r2_hidden(D_82,k1_relat_1(A_81))
      | ~ v1_funct_1(A_81)
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_28,plain,(
    ! [A_45,B_46] :
      ( m1_subset_1(A_45,k1_zfmisc_1(B_46))
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_73,plain,(
    ! [A_71,C_72,B_73] :
      ( m1_subset_1(A_71,C_72)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(C_72))
      | ~ r2_hidden(A_71,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_76,plain,(
    ! [A_71,B_46,A_45] :
      ( m1_subset_1(A_71,B_46)
      | ~ r2_hidden(A_71,A_45)
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(resolution,[status(thm)],[c_28,c_73])).

tff(c_167,plain,(
    ! [A_114,D_115,B_116] :
      ( m1_subset_1(k1_funct_1(A_114,D_115),B_116)
      | ~ r1_tarski(k2_relat_1(A_114),B_116)
      | ~ r2_hidden(D_115,k1_relat_1(A_114))
      | ~ v1_funct_1(A_114)
      | ~ v1_relat_1(A_114) ) ),
    inference(resolution,[status(thm)],[c_89,c_76])).

tff(c_171,plain,(
    ! [B_117,D_118,A_119] :
      ( m1_subset_1(k1_funct_1(B_117,D_118),A_119)
      | ~ r2_hidden(D_118,k1_relat_1(B_117))
      | ~ v1_funct_1(B_117)
      | ~ v5_relat_1(B_117,A_119)
      | ~ v1_relat_1(B_117) ) ),
    inference(resolution,[status(thm)],[c_4,c_167])).

tff(c_181,plain,(
    ! [A_119] :
      ( m1_subset_1(k1_funct_1('#skF_6','#skF_7'),A_119)
      | ~ v1_funct_1('#skF_6')
      | ~ v5_relat_1('#skF_6',A_119)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_36,c_171])).

tff(c_215,plain,(
    ! [A_122] :
      ( m1_subset_1(k1_funct_1('#skF_6','#skF_7'),A_122)
      | ~ v5_relat_1('#skF_6',A_122) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_181])).

tff(c_49,plain,(
    ! [A_58,B_59] :
      ( r2_hidden(A_58,B_59)
      | v1_xboole_0(B_59)
      | ~ m1_subset_1(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_34,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_7'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_53,plain,
    ( v1_xboole_0('#skF_5')
    | ~ m1_subset_1(k1_funct_1('#skF_6','#skF_7'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_49,c_34])).

tff(c_54,plain,(
    ~ m1_subset_1(k1_funct_1('#skF_6','#skF_7'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_53])).

tff(c_230,plain,(
    ~ v5_relat_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_215,c_54])).

tff(c_242,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_230])).

tff(c_243,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_53])).

tff(c_267,plain,(
    ! [A_137,D_138] :
      ( r2_hidden(k1_funct_1(A_137,D_138),k2_relat_1(A_137))
      | ~ r2_hidden(D_138,k1_relat_1(A_137))
      | ~ v1_funct_1(A_137)
      | ~ v1_relat_1(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_246,plain,(
    ! [C_125,B_126,A_127] :
      ( ~ v1_xboole_0(C_125)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(C_125))
      | ~ r2_hidden(A_127,B_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_249,plain,(
    ! [B_46,A_127,A_45] :
      ( ~ v1_xboole_0(B_46)
      | ~ r2_hidden(A_127,A_45)
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(resolution,[status(thm)],[c_28,c_246])).

tff(c_297,plain,(
    ! [B_151,A_152,D_153] :
      ( ~ v1_xboole_0(B_151)
      | ~ r1_tarski(k2_relat_1(A_152),B_151)
      | ~ r2_hidden(D_153,k1_relat_1(A_152))
      | ~ v1_funct_1(A_152)
      | ~ v1_relat_1(A_152) ) ),
    inference(resolution,[status(thm)],[c_267,c_249])).

tff(c_301,plain,(
    ! [A_154,D_155,B_156] :
      ( ~ v1_xboole_0(A_154)
      | ~ r2_hidden(D_155,k1_relat_1(B_156))
      | ~ v1_funct_1(B_156)
      | ~ v5_relat_1(B_156,A_154)
      | ~ v1_relat_1(B_156) ) ),
    inference(resolution,[status(thm)],[c_4,c_297])).

tff(c_308,plain,(
    ! [A_154] :
      ( ~ v1_xboole_0(A_154)
      | ~ v1_funct_1('#skF_6')
      | ~ v5_relat_1('#skF_6',A_154)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_36,c_301])).

tff(c_314,plain,(
    ! [A_157] :
      ( ~ v1_xboole_0(A_157)
      | ~ v5_relat_1('#skF_6',A_157) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_308])).

tff(c_317,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_314])).

tff(c_321,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_317])).

%------------------------------------------------------------------------------
