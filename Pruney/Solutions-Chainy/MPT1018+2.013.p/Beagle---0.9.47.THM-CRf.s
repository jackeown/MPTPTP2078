%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:47 EST 2020

% Result     : Theorem 3.18s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 180 expanded)
%              Number of leaves         :   33 (  80 expanded)
%              Depth                    :   10
%              Number of atoms          :  130 ( 566 expanded)
%              Number of equality atoms :   41 ( 154 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_101,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( v2_funct_1(B)
         => ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A)
                & k1_funct_1(B,C) = k1_funct_1(B,D) )
             => C = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_funct_2)).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_83,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(D)
          & r2_hidden(C,A) )
       => ( B = k1_xboole_0
          | k1_funct_1(k2_funct_1(D),k1_funct_1(D,C)) = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
      <=> ! [B,C] :
            ( ( r2_hidden(B,k1_relat_1(A))
              & r2_hidden(C,k1_relat_1(A))
              & k1_funct_1(A,B) = k1_funct_1(A,C) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

tff(c_34,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_38,plain,(
    r2_hidden('#skF_6','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_16,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_67,plain,(
    ! [B_38,A_39] :
      ( v1_relat_1(B_38)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_39))
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_73,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(resolution,[status(thm)],[c_44,c_67])).

tff(c_77,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_73])).

tff(c_48,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_42,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_46,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_36,plain,(
    k1_funct_1('#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_40,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_610,plain,(
    ! [D_104,C_105,B_106,A_107] :
      ( k1_funct_1(k2_funct_1(D_104),k1_funct_1(D_104,C_105)) = C_105
      | k1_xboole_0 = B_106
      | ~ r2_hidden(C_105,A_107)
      | ~ v2_funct_1(D_104)
      | ~ m1_subset_1(D_104,k1_zfmisc_1(k2_zfmisc_1(A_107,B_106)))
      | ~ v1_funct_2(D_104,A_107,B_106)
      | ~ v1_funct_1(D_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_626,plain,(
    ! [D_108,B_109] :
      ( k1_funct_1(k2_funct_1(D_108),k1_funct_1(D_108,'#skF_5')) = '#skF_5'
      | k1_xboole_0 = B_109
      | ~ v2_funct_1(D_108)
      | ~ m1_subset_1(D_108,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_109)))
      | ~ v1_funct_2(D_108,'#skF_3',B_109)
      | ~ v1_funct_1(D_108) ) ),
    inference(resolution,[status(thm)],[c_40,c_610])).

tff(c_637,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_5')) = '#skF_5'
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_626])).

tff(c_643,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_5'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_42,c_36,c_637])).

tff(c_646,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_643])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_673,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_646,c_8])).

tff(c_130,plain,(
    ! [A_48,B_49,C_50] :
      ( k1_relset_1(A_48,B_49,C_50) = k1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_139,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_130])).

tff(c_144,plain,(
    ! [A_51,B_52,C_53] :
      ( m1_subset_1(k1_relset_1(A_51,B_52,C_53),k1_zfmisc_1(A_51))
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_157,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_144])).

tff(c_162,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_157])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_170,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_162,c_10])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_177,plain,
    ( k1_relat_1('#skF_4') = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_170,c_2])).

tff(c_456,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_177])).

tff(c_681,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_673,c_456])).

tff(c_683,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_643])).

tff(c_682,plain,(
    k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_643])).

tff(c_684,plain,(
    ! [D_113,B_114] :
      ( k1_funct_1(k2_funct_1(D_113),k1_funct_1(D_113,'#skF_6')) = '#skF_6'
      | k1_xboole_0 = B_114
      | ~ v2_funct_1(D_113)
      | ~ m1_subset_1(D_113,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_114)))
      | ~ v1_funct_2(D_113,'#skF_3',B_114)
      | ~ v1_funct_1(D_113) ) ),
    inference(resolution,[status(thm)],[c_38,c_610])).

tff(c_695,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_684])).

tff(c_701,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_42,c_695])).

tff(c_710,plain,
    ( '#skF_5' = '#skF_6'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_682,c_701])).

tff(c_711,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_683,c_34,c_710])).

tff(c_712,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_177])).

tff(c_784,plain,(
    ! [C_119,B_120,A_121] :
      ( C_119 = B_120
      | k1_funct_1(A_121,C_119) != k1_funct_1(A_121,B_120)
      | ~ r2_hidden(C_119,k1_relat_1(A_121))
      | ~ r2_hidden(B_120,k1_relat_1(A_121))
      | ~ v2_funct_1(A_121)
      | ~ v1_funct_1(A_121)
      | ~ v1_relat_1(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_790,plain,(
    ! [B_120] :
      ( B_120 = '#skF_5'
      | k1_funct_1('#skF_4',B_120) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden('#skF_5',k1_relat_1('#skF_4'))
      | ~ r2_hidden(B_120,k1_relat_1('#skF_4'))
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_784])).

tff(c_1163,plain,(
    ! [B_161] :
      ( B_161 = '#skF_5'
      | k1_funct_1('#skF_4',B_161) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden(B_161,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_48,c_42,c_712,c_40,c_712,c_790])).

tff(c_1166,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_38,c_1163])).

tff(c_1173,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_1166])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:53:30 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.18/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/1.56  
% 3.18/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/1.56  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 3.18/1.56  
% 3.18/1.56  %Foreground sorts:
% 3.18/1.56  
% 3.18/1.56  
% 3.18/1.56  %Background operators:
% 3.18/1.56  
% 3.18/1.56  
% 3.18/1.56  %Foreground operators:
% 3.18/1.56  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.18/1.56  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.18/1.56  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.18/1.56  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.18/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.18/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.18/1.56  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.18/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.18/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.18/1.56  tff('#skF_5', type, '#skF_5': $i).
% 3.18/1.56  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.18/1.56  tff('#skF_6', type, '#skF_6': $i).
% 3.18/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.18/1.56  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.18/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.18/1.56  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.18/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.18/1.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.18/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.18/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.18/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.18/1.56  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.18/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.18/1.56  
% 3.36/1.57  tff(f_101, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) => (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_funct_2)).
% 3.36/1.57  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.36/1.57  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.36/1.57  tff(f_83, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(D) & r2_hidden(C, A)) => ((B = k1_xboole_0) | (k1_funct_1(k2_funct_1(D), k1_funct_1(D, C)) = C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_funct_2)).
% 3.36/1.57  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.36/1.57  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.36/1.57  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 3.36/1.57  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.36/1.57  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.36/1.57  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_funct_1)).
% 3.36/1.57  tff(c_34, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.36/1.57  tff(c_38, plain, (r2_hidden('#skF_6', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.36/1.57  tff(c_16, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.36/1.57  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.36/1.57  tff(c_67, plain, (![B_38, A_39]: (v1_relat_1(B_38) | ~m1_subset_1(B_38, k1_zfmisc_1(A_39)) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.36/1.57  tff(c_73, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_44, c_67])).
% 3.36/1.57  tff(c_77, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_73])).
% 3.36/1.57  tff(c_48, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.36/1.57  tff(c_42, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.36/1.57  tff(c_46, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.36/1.57  tff(c_36, plain, (k1_funct_1('#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.36/1.57  tff(c_40, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.36/1.57  tff(c_610, plain, (![D_104, C_105, B_106, A_107]: (k1_funct_1(k2_funct_1(D_104), k1_funct_1(D_104, C_105))=C_105 | k1_xboole_0=B_106 | ~r2_hidden(C_105, A_107) | ~v2_funct_1(D_104) | ~m1_subset_1(D_104, k1_zfmisc_1(k2_zfmisc_1(A_107, B_106))) | ~v1_funct_2(D_104, A_107, B_106) | ~v1_funct_1(D_104))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.36/1.57  tff(c_626, plain, (![D_108, B_109]: (k1_funct_1(k2_funct_1(D_108), k1_funct_1(D_108, '#skF_5'))='#skF_5' | k1_xboole_0=B_109 | ~v2_funct_1(D_108) | ~m1_subset_1(D_108, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_109))) | ~v1_funct_2(D_108, '#skF_3', B_109) | ~v1_funct_1(D_108))), inference(resolution, [status(thm)], [c_40, c_610])).
% 3.36/1.57  tff(c_637, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_5'))='#skF_5' | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_626])).
% 3.36/1.57  tff(c_643, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_5' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_42, c_36, c_637])).
% 3.36/1.57  tff(c_646, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_643])).
% 3.36/1.57  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.36/1.57  tff(c_673, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_646, c_8])).
% 3.36/1.57  tff(c_130, plain, (![A_48, B_49, C_50]: (k1_relset_1(A_48, B_49, C_50)=k1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.36/1.57  tff(c_139, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_130])).
% 3.36/1.57  tff(c_144, plain, (![A_51, B_52, C_53]: (m1_subset_1(k1_relset_1(A_51, B_52, C_53), k1_zfmisc_1(A_51)) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.36/1.57  tff(c_157, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_139, c_144])).
% 3.36/1.57  tff(c_162, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_157])).
% 3.36/1.57  tff(c_10, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.36/1.57  tff(c_170, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_162, c_10])).
% 3.36/1.57  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.36/1.57  tff(c_177, plain, (k1_relat_1('#skF_4')='#skF_3' | ~r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_170, c_2])).
% 3.36/1.57  tff(c_456, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_177])).
% 3.36/1.57  tff(c_681, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_673, c_456])).
% 3.36/1.57  tff(c_683, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_643])).
% 3.36/1.57  tff(c_682, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_643])).
% 3.36/1.57  tff(c_684, plain, (![D_113, B_114]: (k1_funct_1(k2_funct_1(D_113), k1_funct_1(D_113, '#skF_6'))='#skF_6' | k1_xboole_0=B_114 | ~v2_funct_1(D_113) | ~m1_subset_1(D_113, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_114))) | ~v1_funct_2(D_113, '#skF_3', B_114) | ~v1_funct_1(D_113))), inference(resolution, [status(thm)], [c_38, c_610])).
% 3.36/1.57  tff(c_695, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_684])).
% 3.36/1.57  tff(c_701, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_42, c_695])).
% 3.36/1.57  tff(c_710, plain, ('#skF_5'='#skF_6' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_682, c_701])).
% 3.36/1.57  tff(c_711, plain, $false, inference(negUnitSimplification, [status(thm)], [c_683, c_34, c_710])).
% 3.36/1.57  tff(c_712, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_177])).
% 3.36/1.57  tff(c_784, plain, (![C_119, B_120, A_121]: (C_119=B_120 | k1_funct_1(A_121, C_119)!=k1_funct_1(A_121, B_120) | ~r2_hidden(C_119, k1_relat_1(A_121)) | ~r2_hidden(B_120, k1_relat_1(A_121)) | ~v2_funct_1(A_121) | ~v1_funct_1(A_121) | ~v1_relat_1(A_121))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.36/1.57  tff(c_790, plain, (![B_120]: (B_120='#skF_5' | k1_funct_1('#skF_4', B_120)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden('#skF_5', k1_relat_1('#skF_4')) | ~r2_hidden(B_120, k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_784])).
% 3.36/1.57  tff(c_1163, plain, (![B_161]: (B_161='#skF_5' | k1_funct_1('#skF_4', B_161)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden(B_161, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_48, c_42, c_712, c_40, c_712, c_790])).
% 3.36/1.57  tff(c_1166, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_38, c_1163])).
% 3.36/1.57  tff(c_1173, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_1166])).
% 3.36/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.36/1.57  
% 3.36/1.57  Inference rules
% 3.36/1.57  ----------------------
% 3.36/1.57  #Ref     : 3
% 3.36/1.57  #Sup     : 234
% 3.36/1.57  #Fact    : 0
% 3.36/1.57  #Define  : 0
% 3.36/1.57  #Split   : 11
% 3.36/1.57  #Chain   : 0
% 3.36/1.57  #Close   : 0
% 3.36/1.57  
% 3.36/1.57  Ordering : KBO
% 3.36/1.57  
% 3.36/1.57  Simplification rules
% 3.36/1.57  ----------------------
% 3.36/1.57  #Subsume      : 16
% 3.36/1.57  #Demod        : 247
% 3.36/1.57  #Tautology    : 133
% 3.36/1.57  #SimpNegUnit  : 8
% 3.36/1.57  #BackRed      : 45
% 3.36/1.57  
% 3.36/1.57  #Partial instantiations: 0
% 3.36/1.57  #Strategies tried      : 1
% 3.36/1.57  
% 3.36/1.57  Timing (in seconds)
% 3.36/1.57  ----------------------
% 3.36/1.58  Preprocessing        : 0.33
% 3.36/1.58  Parsing              : 0.18
% 3.36/1.58  CNF conversion       : 0.02
% 3.36/1.58  Main loop            : 0.42
% 3.36/1.58  Inferencing          : 0.15
% 3.36/1.58  Reduction            : 0.14
% 3.36/1.58  Demodulation         : 0.10
% 3.36/1.58  BG Simplification    : 0.02
% 3.36/1.58  Subsumption          : 0.07
% 3.36/1.58  Abstraction          : 0.02
% 3.36/1.58  MUC search           : 0.00
% 3.36/1.58  Cooper               : 0.00
% 3.36/1.58  Total                : 0.79
% 3.36/1.58  Index Insertion      : 0.00
% 3.36/1.58  Index Deletion       : 0.00
% 3.36/1.58  Index Matching       : 0.00
% 3.36/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
