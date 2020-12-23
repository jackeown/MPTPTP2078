%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:50 EST 2020

% Result     : Theorem 4.63s
% Output     : CNFRefutation 4.77s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 974 expanded)
%              Number of leaves         :   37 ( 357 expanded)
%              Depth                    :   20
%              Number of atoms          :  389 (4491 expanded)
%              Number of equality atoms :   34 ( 575 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_132,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & v2_pre_topc(C)
                  & l1_pre_topc(C) )
               => ( ( u1_struct_0(A) = u1_struct_0(B)
                    & r1_tarski(u1_pre_topc(B),u1_pre_topc(A)) )
                 => ! [D] :
                      ( ( v1_funct_1(D)
                        & v1_funct_2(D,u1_struct_0(B),u1_struct_0(C))
                        & v5_pre_topc(D,B,C)
                        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(C)))) )
                     => ( v1_funct_1(D)
                        & v1_funct_2(D,u1_struct_0(A),u1_struct_0(C))
                        & v5_pre_topc(D,A,C)
                        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(C)))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_tmap_1)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( ( k2_struct_0(B) = k1_xboole_0
                 => k2_struct_0(A) = k1_xboole_0 )
               => ( v5_pre_topc(C,A,B)
                <=> ! [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                     => ( v3_pre_topc(D,B)
                       => v3_pre_topc(k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,D),A) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_2)).

tff(f_37,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k8_relset_1(A,B,C,D),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relset_1)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_62,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_46,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_44,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_50,plain,(
    u1_struct_0('#skF_3') = u1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_40,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_38,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_5'))))
    | ~ v5_pre_topc('#skF_6','#skF_3','#skF_5')
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_70,plain,(
    ~ v5_pre_topc('#skF_6','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_50,c_40,c_50,c_38])).

tff(c_58,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_18,plain,(
    ! [A_14] :
      ( l1_struct_0(A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_76,plain,(
    ! [A_50] :
      ( u1_struct_0(A_50) = k2_struct_0(A_50)
      | ~ l1_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_81,plain,(
    ! [A_51] :
      ( u1_struct_0(A_51) = k2_struct_0(A_51)
      | ~ l1_pre_topc(A_51) ) ),
    inference(resolution,[status(thm)],[c_18,c_76])).

tff(c_92,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_81])).

tff(c_52,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_93,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_81])).

tff(c_100,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),k2_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_44])).

tff(c_163,plain,(
    v1_funct_2('#skF_6',k2_struct_0('#skF_4'),k2_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_100])).

tff(c_99,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),k2_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_40])).

tff(c_171,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_99])).

tff(c_64,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_91,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_81])).

tff(c_94,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_50])).

tff(c_109,plain,(
    k2_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_94])).

tff(c_110,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_91])).

tff(c_366,plain,(
    ! [A_112,B_113,C_114] :
      ( k2_struct_0(A_112) != k1_xboole_0
      | v3_pre_topc('#skF_2'(A_112,B_113,C_114),B_113)
      | v5_pre_topc(C_114,A_112,B_113)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_112),u1_struct_0(B_113))))
      | ~ v1_funct_2(C_114,u1_struct_0(A_112),u1_struct_0(B_113))
      | ~ v1_funct_1(C_114)
      | ~ l1_pre_topc(B_113)
      | ~ l1_pre_topc(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_377,plain,(
    ! [A_112,C_114] :
      ( k2_struct_0(A_112) != k1_xboole_0
      | v3_pre_topc('#skF_2'(A_112,'#skF_4',C_114),'#skF_4')
      | v5_pre_topc(C_114,A_112,'#skF_4')
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_112),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_114,u1_struct_0(A_112),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_114)
      | ~ l1_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_112) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_366])).

tff(c_427,plain,(
    ! [A_125,C_126] :
      ( k2_struct_0(A_125) != k1_xboole_0
      | v3_pre_topc('#skF_2'(A_125,'#skF_4',C_126),'#skF_4')
      | v5_pre_topc(C_126,A_125,'#skF_4')
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_125),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_126,u1_struct_0(A_125),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(C_126)
      | ~ l1_pre_topc(A_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_92,c_377])).

tff(c_440,plain,(
    ! [C_126] :
      ( k2_struct_0('#skF_5') != k1_xboole_0
      | v3_pre_topc('#skF_2'('#skF_5','#skF_4',C_126),'#skF_4')
      | v5_pre_topc(C_126,'#skF_5','#skF_4')
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_5'),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_126,u1_struct_0('#skF_5'),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(C_126)
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_427])).

tff(c_447,plain,(
    ! [C_126] :
      ( k2_struct_0('#skF_5') != k1_xboole_0
      | v3_pre_topc('#skF_2'('#skF_5','#skF_4',C_126),'#skF_4')
      | v5_pre_topc(C_126,'#skF_5','#skF_4')
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_5'),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_126,k2_struct_0('#skF_5'),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(C_126) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_93,c_440])).

tff(c_514,plain,(
    k2_struct_0('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_447])).

tff(c_484,plain,(
    ! [B_148,A_149,C_150] :
      ( k2_struct_0(B_148) = k1_xboole_0
      | m1_subset_1('#skF_2'(A_149,B_148,C_150),k1_zfmisc_1(u1_struct_0(B_148)))
      | v5_pre_topc(C_150,A_149,B_148)
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_149),u1_struct_0(B_148))))
      | ~ v1_funct_2(C_150,u1_struct_0(A_149),u1_struct_0(B_148))
      | ~ v1_funct_1(C_150)
      | ~ l1_pre_topc(B_148)
      | ~ l1_pre_topc(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_499,plain,(
    ! [A_149,C_150] :
      ( k2_struct_0('#skF_5') = k1_xboole_0
      | m1_subset_1('#skF_2'(A_149,'#skF_5',C_150),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v5_pre_topc(C_150,A_149,'#skF_5')
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_149),k2_struct_0('#skF_5'))))
      | ~ v1_funct_2(C_150,u1_struct_0(A_149),u1_struct_0('#skF_5'))
      | ~ v1_funct_1(C_150)
      | ~ l1_pre_topc('#skF_5')
      | ~ l1_pre_topc(A_149) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_484])).

tff(c_512,plain,(
    ! [A_149,C_150] :
      ( k2_struct_0('#skF_5') = k1_xboole_0
      | m1_subset_1('#skF_2'(A_149,'#skF_5',C_150),k1_zfmisc_1(k2_struct_0('#skF_5')))
      | v5_pre_topc(C_150,A_149,'#skF_5')
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_149),k2_struct_0('#skF_5'))))
      | ~ v1_funct_2(C_150,u1_struct_0(A_149),k2_struct_0('#skF_5'))
      | ~ v1_funct_1(C_150)
      | ~ l1_pre_topc(A_149) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_93,c_93,c_499])).

tff(c_790,plain,(
    ! [A_180,C_181] :
      ( m1_subset_1('#skF_2'(A_180,'#skF_5',C_181),k1_zfmisc_1(k2_struct_0('#skF_5')))
      | v5_pre_topc(C_181,A_180,'#skF_5')
      | ~ m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_180),k2_struct_0('#skF_5'))))
      | ~ v1_funct_2(C_181,u1_struct_0(A_180),k2_struct_0('#skF_5'))
      | ~ v1_funct_1(C_181)
      | ~ l1_pre_topc(A_180) ) ),
    inference(negUnitSimplification,[status(thm)],[c_514,c_512])).

tff(c_797,plain,(
    ! [C_181] :
      ( m1_subset_1('#skF_2'('#skF_3','#skF_5',C_181),k1_zfmisc_1(k2_struct_0('#skF_5')))
      | v5_pre_topc(C_181,'#skF_3','#skF_5')
      | ~ m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_5'))))
      | ~ v1_funct_2(C_181,u1_struct_0('#skF_3'),k2_struct_0('#skF_5'))
      | ~ v1_funct_1(C_181)
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_790])).

tff(c_845,plain,(
    ! [C_185] :
      ( m1_subset_1('#skF_2'('#skF_3','#skF_5',C_185),k1_zfmisc_1(k2_struct_0('#skF_5')))
      | v5_pre_topc(C_185,'#skF_3','#skF_5')
      | ~ m1_subset_1(C_185,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_5'))))
      | ~ v1_funct_2(C_185,k2_struct_0('#skF_4'),k2_struct_0('#skF_5'))
      | ~ v1_funct_1(C_185) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_110,c_797])).

tff(c_852,plain,
    ( m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_struct_0('#skF_5')))
    | v5_pre_topc('#skF_6','#skF_3','#skF_5')
    | ~ v1_funct_2('#skF_6',k2_struct_0('#skF_4'),k2_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_171,c_845])).

tff(c_856,plain,
    ( m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_struct_0('#skF_5')))
    | v5_pre_topc('#skF_6','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_163,c_852])).

tff(c_857,plain,(
    m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_856])).

tff(c_293,plain,(
    ! [B_88,A_89,C_90] :
      ( k2_struct_0(B_88) = k1_xboole_0
      | v3_pre_topc('#skF_2'(A_89,B_88,C_90),B_88)
      | v5_pre_topc(C_90,A_89,B_88)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_89),u1_struct_0(B_88))))
      | ~ v1_funct_2(C_90,u1_struct_0(A_89),u1_struct_0(B_88))
      | ~ v1_funct_1(C_90)
      | ~ l1_pre_topc(B_88)
      | ~ l1_pre_topc(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_298,plain,(
    ! [B_88,C_90] :
      ( k2_struct_0(B_88) = k1_xboole_0
      | v3_pre_topc('#skF_2'('#skF_3',B_88,C_90),B_88)
      | v5_pre_topc(C_90,'#skF_3',B_88)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),u1_struct_0(B_88))))
      | ~ v1_funct_2(C_90,u1_struct_0('#skF_3'),u1_struct_0(B_88))
      | ~ v1_funct_1(C_90)
      | ~ l1_pre_topc(B_88)
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_293])).

tff(c_622,plain,(
    ! [B_163,C_164] :
      ( k2_struct_0(B_163) = k1_xboole_0
      | v3_pre_topc('#skF_2'('#skF_3',B_163,C_164),B_163)
      | v5_pre_topc(C_164,'#skF_3',B_163)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),u1_struct_0(B_163))))
      | ~ v1_funct_2(C_164,k2_struct_0('#skF_4'),u1_struct_0(B_163))
      | ~ v1_funct_1(C_164)
      | ~ l1_pre_topc(B_163) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_110,c_298])).

tff(c_631,plain,(
    ! [C_164] :
      ( k2_struct_0('#skF_5') = k1_xboole_0
      | v3_pre_topc('#skF_2'('#skF_3','#skF_5',C_164),'#skF_5')
      | v5_pre_topc(C_164,'#skF_3','#skF_5')
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_5'))))
      | ~ v1_funct_2(C_164,k2_struct_0('#skF_4'),u1_struct_0('#skF_5'))
      | ~ v1_funct_1(C_164)
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_622])).

tff(c_640,plain,(
    ! [C_164] :
      ( k2_struct_0('#skF_5') = k1_xboole_0
      | v3_pre_topc('#skF_2'('#skF_3','#skF_5',C_164),'#skF_5')
      | v5_pre_topc(C_164,'#skF_3','#skF_5')
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_5'))))
      | ~ v1_funct_2(C_164,k2_struct_0('#skF_4'),k2_struct_0('#skF_5'))
      | ~ v1_funct_1(C_164) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_93,c_631])).

tff(c_648,plain,(
    ! [C_166] :
      ( v3_pre_topc('#skF_2'('#skF_3','#skF_5',C_166),'#skF_5')
      | v5_pre_topc(C_166,'#skF_3','#skF_5')
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_5'))))
      | ~ v1_funct_2(C_166,k2_struct_0('#skF_4'),k2_struct_0('#skF_5'))
      | ~ v1_funct_1(C_166) ) ),
    inference(negUnitSimplification,[status(thm)],[c_514,c_640])).

tff(c_655,plain,
    ( v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6'),'#skF_5')
    | v5_pre_topc('#skF_6','#skF_3','#skF_5')
    | ~ v1_funct_2('#skF_6',k2_struct_0('#skF_4'),k2_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_171,c_648])).

tff(c_659,plain,
    ( v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6'),'#skF_5')
    | v5_pre_topc('#skF_6','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_163,c_655])).

tff(c_660,plain,(
    v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_659])).

tff(c_48,plain,(
    r1_tarski(u1_pre_topc('#skF_4'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_42,plain,(
    v5_pre_topc('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1032,plain,(
    ! [B_206,A_207,C_208,D_209] :
      ( k2_struct_0(B_206) = k1_xboole_0
      | v3_pre_topc(k8_relset_1(u1_struct_0(A_207),u1_struct_0(B_206),C_208,D_209),A_207)
      | ~ v3_pre_topc(D_209,B_206)
      | ~ m1_subset_1(D_209,k1_zfmisc_1(u1_struct_0(B_206)))
      | ~ v5_pre_topc(C_208,A_207,B_206)
      | ~ m1_subset_1(C_208,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_207),u1_struct_0(B_206))))
      | ~ v1_funct_2(C_208,u1_struct_0(A_207),u1_struct_0(B_206))
      | ~ v1_funct_1(C_208)
      | ~ l1_pre_topc(B_206)
      | ~ l1_pre_topc(A_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1047,plain,(
    ! [A_207,C_208,D_209] :
      ( k2_struct_0('#skF_5') = k1_xboole_0
      | v3_pre_topc(k8_relset_1(u1_struct_0(A_207),u1_struct_0('#skF_5'),C_208,D_209),A_207)
      | ~ v3_pre_topc(D_209,'#skF_5')
      | ~ m1_subset_1(D_209,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v5_pre_topc(C_208,A_207,'#skF_5')
      | ~ m1_subset_1(C_208,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_207),k2_struct_0('#skF_5'))))
      | ~ v1_funct_2(C_208,u1_struct_0(A_207),u1_struct_0('#skF_5'))
      | ~ v1_funct_1(C_208)
      | ~ l1_pre_topc('#skF_5')
      | ~ l1_pre_topc(A_207) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_1032])).

tff(c_1062,plain,(
    ! [A_207,C_208,D_209] :
      ( k2_struct_0('#skF_5') = k1_xboole_0
      | v3_pre_topc(k8_relset_1(u1_struct_0(A_207),k2_struct_0('#skF_5'),C_208,D_209),A_207)
      | ~ v3_pre_topc(D_209,'#skF_5')
      | ~ m1_subset_1(D_209,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ v5_pre_topc(C_208,A_207,'#skF_5')
      | ~ m1_subset_1(C_208,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_207),k2_struct_0('#skF_5'))))
      | ~ v1_funct_2(C_208,u1_struct_0(A_207),k2_struct_0('#skF_5'))
      | ~ v1_funct_1(C_208)
      | ~ l1_pre_topc(A_207) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_93,c_93,c_93,c_1047])).

tff(c_1334,plain,(
    ! [A_247,C_248,D_249] :
      ( v3_pre_topc(k8_relset_1(u1_struct_0(A_247),k2_struct_0('#skF_5'),C_248,D_249),A_247)
      | ~ v3_pre_topc(D_249,'#skF_5')
      | ~ m1_subset_1(D_249,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ v5_pre_topc(C_248,A_247,'#skF_5')
      | ~ m1_subset_1(C_248,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_247),k2_struct_0('#skF_5'))))
      | ~ v1_funct_2(C_248,u1_struct_0(A_247),k2_struct_0('#skF_5'))
      | ~ v1_funct_1(C_248)
      | ~ l1_pre_topc(A_247) ) ),
    inference(negUnitSimplification,[status(thm)],[c_514,c_1062])).

tff(c_1341,plain,(
    ! [C_248,D_249] :
      ( v3_pre_topc(k8_relset_1(u1_struct_0('#skF_4'),k2_struct_0('#skF_5'),C_248,D_249),'#skF_4')
      | ~ v3_pre_topc(D_249,'#skF_5')
      | ~ m1_subset_1(D_249,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ v5_pre_topc(C_248,'#skF_4','#skF_5')
      | ~ m1_subset_1(C_248,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_5'))))
      | ~ v1_funct_2(C_248,u1_struct_0('#skF_4'),k2_struct_0('#skF_5'))
      | ~ v1_funct_1(C_248)
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_1334])).

tff(c_1415,plain,(
    ! [C_257,D_258] :
      ( v3_pre_topc(k8_relset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_5'),C_257,D_258),'#skF_4')
      | ~ v3_pre_topc(D_258,'#skF_5')
      | ~ m1_subset_1(D_258,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ v5_pre_topc(C_257,'#skF_4','#skF_5')
      | ~ m1_subset_1(C_257,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_5'))))
      | ~ v1_funct_2(C_257,k2_struct_0('#skF_4'),k2_struct_0('#skF_5'))
      | ~ v1_funct_1(C_257) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_92,c_92,c_1341])).

tff(c_1420,plain,(
    ! [D_258] :
      ( v3_pre_topc(k8_relset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_5'),'#skF_6',D_258),'#skF_4')
      | ~ v3_pre_topc(D_258,'#skF_5')
      | ~ m1_subset_1(D_258,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ v5_pre_topc('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_2('#skF_6',k2_struct_0('#skF_4'),k2_struct_0('#skF_5'))
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_171,c_1415])).

tff(c_1425,plain,(
    ! [D_259] :
      ( v3_pre_topc(k8_relset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_5'),'#skF_6',D_259),'#skF_4')
      | ~ v3_pre_topc(D_259,'#skF_5')
      | ~ m1_subset_1(D_259,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_163,c_42,c_1420])).

tff(c_10,plain,(
    ! [A_6,B_7,C_8,D_9] :
      ( m1_subset_1(k8_relset_1(A_6,B_7,C_8,D_9),k1_zfmisc_1(A_6))
      | ~ m1_subset_1(C_8,k1_zfmisc_1(k2_zfmisc_1(A_6,B_7))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_186,plain,(
    ! [B_68,A_69] :
      ( r2_hidden(B_68,u1_pre_topc(A_69))
      | ~ v3_pre_topc(B_68,A_69)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_196,plain,(
    ! [B_68] :
      ( r2_hidden(B_68,u1_pre_topc('#skF_4'))
      | ~ v3_pre_topc(B_68,'#skF_4')
      | ~ m1_subset_1(B_68,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_186])).

tff(c_234,plain,(
    ! [B_73] :
      ( r2_hidden(B_73,u1_pre_topc('#skF_4'))
      | ~ v3_pre_topc(B_73,'#skF_4')
      | ~ m1_subset_1(B_73,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_196])).

tff(c_400,plain,(
    ! [B_118,C_119,D_120] :
      ( r2_hidden(k8_relset_1(k2_struct_0('#skF_4'),B_118,C_119,D_120),u1_pre_topc('#skF_4'))
      | ~ v3_pre_topc(k8_relset_1(k2_struct_0('#skF_4'),B_118,C_119,D_120),'#skF_4')
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),B_118))) ) ),
    inference(resolution,[status(thm)],[c_10,c_234])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_407,plain,(
    ! [B_118,C_119,D_120,B_2] :
      ( r2_hidden(k8_relset_1(k2_struct_0('#skF_4'),B_118,C_119,D_120),B_2)
      | ~ r1_tarski(u1_pre_topc('#skF_4'),B_2)
      | ~ v3_pre_topc(k8_relset_1(k2_struct_0('#skF_4'),B_118,C_119,D_120),'#skF_4')
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),B_118))) ) ),
    inference(resolution,[status(thm)],[c_400,c_2])).

tff(c_1431,plain,(
    ! [D_259,B_2] :
      ( r2_hidden(k8_relset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_5'),'#skF_6',D_259),B_2)
      | ~ r1_tarski(u1_pre_topc('#skF_4'),B_2)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_5'))))
      | ~ v3_pre_topc(D_259,'#skF_5')
      | ~ m1_subset_1(D_259,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_1425,c_407])).

tff(c_1438,plain,(
    ! [D_260,B_261] :
      ( r2_hidden(k8_relset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_5'),'#skF_6',D_260),B_261)
      | ~ r1_tarski(u1_pre_topc('#skF_4'),B_261)
      | ~ v3_pre_topc(D_260,'#skF_5')
      | ~ m1_subset_1(D_260,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_1431])).

tff(c_213,plain,(
    ! [B_71,A_72] :
      ( v3_pre_topc(B_71,A_72)
      | ~ r2_hidden(B_71,u1_pre_topc(A_72))
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_220,plain,(
    ! [B_71] :
      ( v3_pre_topc(B_71,'#skF_3')
      | ~ r2_hidden(B_71,u1_pre_topc('#skF_3'))
      | ~ m1_subset_1(B_71,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_213])).

tff(c_258,plain,(
    ! [B_77] :
      ( v3_pre_topc(B_77,'#skF_3')
      | ~ r2_hidden(B_77,u1_pre_topc('#skF_3'))
      | ~ m1_subset_1(B_77,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_220])).

tff(c_263,plain,(
    ! [B_7,C_8,D_9] :
      ( v3_pre_topc(k8_relset_1(k2_struct_0('#skF_4'),B_7,C_8,D_9),'#skF_3')
      | ~ r2_hidden(k8_relset_1(k2_struct_0('#skF_4'),B_7,C_8,D_9),u1_pre_topc('#skF_3'))
      | ~ m1_subset_1(C_8,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),B_7))) ) ),
    inference(resolution,[status(thm)],[c_10,c_258])).

tff(c_1442,plain,(
    ! [D_260] :
      ( v3_pre_topc(k8_relset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_5'),'#skF_6',D_260),'#skF_3')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_5'))))
      | ~ r1_tarski(u1_pre_topc('#skF_4'),u1_pre_topc('#skF_3'))
      | ~ v3_pre_topc(D_260,'#skF_5')
      | ~ m1_subset_1(D_260,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_1438,c_263])).

tff(c_1461,plain,(
    ! [D_264] :
      ( v3_pre_topc(k8_relset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_5'),'#skF_6',D_264),'#skF_3')
      | ~ v3_pre_topc(D_264,'#skF_5')
      | ~ m1_subset_1(D_264,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_171,c_1442])).

tff(c_811,plain,(
    ! [B_182,A_183,C_184] :
      ( k2_struct_0(B_182) = k1_xboole_0
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(A_183),u1_struct_0(B_182),C_184,'#skF_2'(A_183,B_182,C_184)),A_183)
      | v5_pre_topc(C_184,A_183,B_182)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_183),u1_struct_0(B_182))))
      | ~ v1_funct_2(C_184,u1_struct_0(A_183),u1_struct_0(B_182))
      | ~ v1_funct_1(C_184)
      | ~ l1_pre_topc(B_182)
      | ~ l1_pre_topc(A_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_829,plain,(
    ! [A_183,C_184] :
      ( k2_struct_0('#skF_5') = k1_xboole_0
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(A_183),k2_struct_0('#skF_5'),C_184,'#skF_2'(A_183,'#skF_5',C_184)),A_183)
      | v5_pre_topc(C_184,A_183,'#skF_5')
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_183),u1_struct_0('#skF_5'))))
      | ~ v1_funct_2(C_184,u1_struct_0(A_183),u1_struct_0('#skF_5'))
      | ~ v1_funct_1(C_184)
      | ~ l1_pre_topc('#skF_5')
      | ~ l1_pre_topc(A_183) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_811])).

tff(c_843,plain,(
    ! [A_183,C_184] :
      ( k2_struct_0('#skF_5') = k1_xboole_0
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(A_183),k2_struct_0('#skF_5'),C_184,'#skF_2'(A_183,'#skF_5',C_184)),A_183)
      | v5_pre_topc(C_184,A_183,'#skF_5')
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_183),k2_struct_0('#skF_5'))))
      | ~ v1_funct_2(C_184,u1_struct_0(A_183),k2_struct_0('#skF_5'))
      | ~ v1_funct_1(C_184)
      | ~ l1_pre_topc(A_183) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_93,c_93,c_829])).

tff(c_1116,plain,(
    ! [A_216,C_217] :
      ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(A_216),k2_struct_0('#skF_5'),C_217,'#skF_2'(A_216,'#skF_5',C_217)),A_216)
      | v5_pre_topc(C_217,A_216,'#skF_5')
      | ~ m1_subset_1(C_217,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_216),k2_struct_0('#skF_5'))))
      | ~ v1_funct_2(C_217,u1_struct_0(A_216),k2_struct_0('#skF_5'))
      | ~ v1_funct_1(C_217)
      | ~ l1_pre_topc(A_216) ) ),
    inference(negUnitSimplification,[status(thm)],[c_514,c_843])).

tff(c_1119,plain,(
    ! [C_217] :
      ( ~ v3_pre_topc(k8_relset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_5'),C_217,'#skF_2'('#skF_3','#skF_5',C_217)),'#skF_3')
      | v5_pre_topc(C_217,'#skF_3','#skF_5')
      | ~ m1_subset_1(C_217,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),k2_struct_0('#skF_5'))))
      | ~ v1_funct_2(C_217,u1_struct_0('#skF_3'),k2_struct_0('#skF_5'))
      | ~ v1_funct_1(C_217)
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_1116])).

tff(c_1127,plain,(
    ! [C_217] :
      ( ~ v3_pre_topc(k8_relset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_5'),C_217,'#skF_2'('#skF_3','#skF_5',C_217)),'#skF_3')
      | v5_pre_topc(C_217,'#skF_3','#skF_5')
      | ~ m1_subset_1(C_217,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_5'))))
      | ~ v1_funct_2(C_217,k2_struct_0('#skF_4'),k2_struct_0('#skF_5'))
      | ~ v1_funct_1(C_217) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_110,c_110,c_1119])).

tff(c_1465,plain,
    ( v5_pre_topc('#skF_6','#skF_3','#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_5'))))
    | ~ v1_funct_2('#skF_6',k2_struct_0('#skF_4'),k2_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6'),'#skF_5')
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_1461,c_1127])).

tff(c_1470,plain,(
    v5_pre_topc('#skF_6','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_857,c_660,c_46,c_163,c_171,c_1465])).

tff(c_1472,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1470])).

tff(c_1474,plain,(
    k2_struct_0('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_447])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_119,plain,(
    ! [A_52] :
      ( ~ v1_xboole_0(u1_struct_0(A_52))
      | ~ l1_struct_0(A_52)
      | v2_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_128,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_5'))
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_119])).

tff(c_131,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_5'))
    | ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_128])).

tff(c_147,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_131])).

tff(c_150,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_147])).

tff(c_154,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_150])).

tff(c_155,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_131])).

tff(c_1482,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1474,c_155])).

tff(c_1486,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1482])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:23:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.63/1.82  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.63/1.83  
% 4.63/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.63/1.83  %$ v5_pre_topc > v1_funct_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 4.63/1.83  
% 4.63/1.83  %Foreground sorts:
% 4.63/1.83  
% 4.63/1.83  
% 4.63/1.83  %Background operators:
% 4.63/1.83  
% 4.63/1.83  
% 4.63/1.83  %Foreground operators:
% 4.63/1.83  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.63/1.83  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 4.63/1.83  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.63/1.83  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.63/1.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.63/1.83  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.63/1.83  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 4.63/1.83  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.63/1.83  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.63/1.83  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.63/1.83  tff('#skF_5', type, '#skF_5': $i).
% 4.63/1.83  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.63/1.83  tff('#skF_6', type, '#skF_6': $i).
% 4.63/1.83  tff('#skF_3', type, '#skF_3': $i).
% 4.63/1.83  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.63/1.83  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.63/1.83  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.63/1.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.63/1.83  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.63/1.83  tff('#skF_4', type, '#skF_4': $i).
% 4.63/1.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.63/1.83  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 4.63/1.83  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.63/1.83  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.63/1.83  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.63/1.83  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.63/1.83  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.63/1.83  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.63/1.83  
% 4.77/1.86  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.77/1.86  tff(f_132, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((~v2_struct_0(C) & v2_pre_topc(C)) & l1_pre_topc(C)) => (((u1_struct_0(A) = u1_struct_0(B)) & r1_tarski(u1_pre_topc(B), u1_pre_topc(A))) => (![D]: ((((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(C))) & v5_pre_topc(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(C))))) => (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(A), u1_struct_0(C))) & v5_pre_topc(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(C)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_tmap_1)).
% 4.77/1.86  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.77/1.86  tff(f_41, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 4.77/1.86  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_struct_0(B) = k1_xboole_0) => (k2_struct_0(A) = k1_xboole_0)) => (v5_pre_topc(C, A, B) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (v3_pre_topc(D, B) => v3_pre_topc(k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D), A)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tops_2)).
% 4.77/1.86  tff(f_37, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k8_relset_1(A, B, C, D), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relset_1)).
% 4.77/1.86  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 4.77/1.86  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.77/1.86  tff(f_62, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.77/1.86  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.77/1.86  tff(c_46, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.77/1.86  tff(c_44, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.77/1.86  tff(c_50, plain, (u1_struct_0('#skF_3')=u1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.77/1.86  tff(c_40, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.77/1.86  tff(c_38, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_5')))) | ~v5_pre_topc('#skF_6', '#skF_3', '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.77/1.86  tff(c_70, plain, (~v5_pre_topc('#skF_6', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_50, c_40, c_50, c_38])).
% 4.77/1.86  tff(c_58, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.77/1.86  tff(c_18, plain, (![A_14]: (l1_struct_0(A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.77/1.86  tff(c_76, plain, (![A_50]: (u1_struct_0(A_50)=k2_struct_0(A_50) | ~l1_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.77/1.86  tff(c_81, plain, (![A_51]: (u1_struct_0(A_51)=k2_struct_0(A_51) | ~l1_pre_topc(A_51))), inference(resolution, [status(thm)], [c_18, c_76])).
% 4.77/1.86  tff(c_92, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_58, c_81])).
% 4.77/1.86  tff(c_52, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.77/1.86  tff(c_93, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_52, c_81])).
% 4.77/1.86  tff(c_100, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), k2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_44])).
% 4.77/1.86  tff(c_163, plain, (v1_funct_2('#skF_6', k2_struct_0('#skF_4'), k2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_100])).
% 4.77/1.86  tff(c_99, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_40])).
% 4.77/1.86  tff(c_171, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_99])).
% 4.77/1.86  tff(c_64, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.77/1.86  tff(c_91, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_64, c_81])).
% 4.77/1.86  tff(c_94, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_50])).
% 4.77/1.86  tff(c_109, plain, (k2_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_94])).
% 4.77/1.86  tff(c_110, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_109, c_91])).
% 4.77/1.86  tff(c_366, plain, (![A_112, B_113, C_114]: (k2_struct_0(A_112)!=k1_xboole_0 | v3_pre_topc('#skF_2'(A_112, B_113, C_114), B_113) | v5_pre_topc(C_114, A_112, B_113) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_112), u1_struct_0(B_113)))) | ~v1_funct_2(C_114, u1_struct_0(A_112), u1_struct_0(B_113)) | ~v1_funct_1(C_114) | ~l1_pre_topc(B_113) | ~l1_pre_topc(A_112))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.77/1.86  tff(c_377, plain, (![A_112, C_114]: (k2_struct_0(A_112)!=k1_xboole_0 | v3_pre_topc('#skF_2'(A_112, '#skF_4', C_114), '#skF_4') | v5_pre_topc(C_114, A_112, '#skF_4') | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_112), k2_struct_0('#skF_4')))) | ~v1_funct_2(C_114, u1_struct_0(A_112), u1_struct_0('#skF_4')) | ~v1_funct_1(C_114) | ~l1_pre_topc('#skF_4') | ~l1_pre_topc(A_112))), inference(superposition, [status(thm), theory('equality')], [c_92, c_366])).
% 4.77/1.86  tff(c_427, plain, (![A_125, C_126]: (k2_struct_0(A_125)!=k1_xboole_0 | v3_pre_topc('#skF_2'(A_125, '#skF_4', C_126), '#skF_4') | v5_pre_topc(C_126, A_125, '#skF_4') | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_125), k2_struct_0('#skF_4')))) | ~v1_funct_2(C_126, u1_struct_0(A_125), k2_struct_0('#skF_4')) | ~v1_funct_1(C_126) | ~l1_pre_topc(A_125))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_92, c_377])).
% 4.77/1.86  tff(c_440, plain, (![C_126]: (k2_struct_0('#skF_5')!=k1_xboole_0 | v3_pre_topc('#skF_2'('#skF_5', '#skF_4', C_126), '#skF_4') | v5_pre_topc(C_126, '#skF_5', '#skF_4') | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_5'), k2_struct_0('#skF_4')))) | ~v1_funct_2(C_126, u1_struct_0('#skF_5'), k2_struct_0('#skF_4')) | ~v1_funct_1(C_126) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_93, c_427])).
% 4.77/1.86  tff(c_447, plain, (![C_126]: (k2_struct_0('#skF_5')!=k1_xboole_0 | v3_pre_topc('#skF_2'('#skF_5', '#skF_4', C_126), '#skF_4') | v5_pre_topc(C_126, '#skF_5', '#skF_4') | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_5'), k2_struct_0('#skF_4')))) | ~v1_funct_2(C_126, k2_struct_0('#skF_5'), k2_struct_0('#skF_4')) | ~v1_funct_1(C_126))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_93, c_440])).
% 4.77/1.86  tff(c_514, plain, (k2_struct_0('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_447])).
% 4.77/1.86  tff(c_484, plain, (![B_148, A_149, C_150]: (k2_struct_0(B_148)=k1_xboole_0 | m1_subset_1('#skF_2'(A_149, B_148, C_150), k1_zfmisc_1(u1_struct_0(B_148))) | v5_pre_topc(C_150, A_149, B_148) | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_149), u1_struct_0(B_148)))) | ~v1_funct_2(C_150, u1_struct_0(A_149), u1_struct_0(B_148)) | ~v1_funct_1(C_150) | ~l1_pre_topc(B_148) | ~l1_pre_topc(A_149))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.77/1.86  tff(c_499, plain, (![A_149, C_150]: (k2_struct_0('#skF_5')=k1_xboole_0 | m1_subset_1('#skF_2'(A_149, '#skF_5', C_150), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v5_pre_topc(C_150, A_149, '#skF_5') | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_149), k2_struct_0('#skF_5')))) | ~v1_funct_2(C_150, u1_struct_0(A_149), u1_struct_0('#skF_5')) | ~v1_funct_1(C_150) | ~l1_pre_topc('#skF_5') | ~l1_pre_topc(A_149))), inference(superposition, [status(thm), theory('equality')], [c_93, c_484])).
% 4.77/1.86  tff(c_512, plain, (![A_149, C_150]: (k2_struct_0('#skF_5')=k1_xboole_0 | m1_subset_1('#skF_2'(A_149, '#skF_5', C_150), k1_zfmisc_1(k2_struct_0('#skF_5'))) | v5_pre_topc(C_150, A_149, '#skF_5') | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_149), k2_struct_0('#skF_5')))) | ~v1_funct_2(C_150, u1_struct_0(A_149), k2_struct_0('#skF_5')) | ~v1_funct_1(C_150) | ~l1_pre_topc(A_149))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_93, c_93, c_499])).
% 4.77/1.86  tff(c_790, plain, (![A_180, C_181]: (m1_subset_1('#skF_2'(A_180, '#skF_5', C_181), k1_zfmisc_1(k2_struct_0('#skF_5'))) | v5_pre_topc(C_181, A_180, '#skF_5') | ~m1_subset_1(C_181, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_180), k2_struct_0('#skF_5')))) | ~v1_funct_2(C_181, u1_struct_0(A_180), k2_struct_0('#skF_5')) | ~v1_funct_1(C_181) | ~l1_pre_topc(A_180))), inference(negUnitSimplification, [status(thm)], [c_514, c_512])).
% 4.77/1.86  tff(c_797, plain, (![C_181]: (m1_subset_1('#skF_2'('#skF_3', '#skF_5', C_181), k1_zfmisc_1(k2_struct_0('#skF_5'))) | v5_pre_topc(C_181, '#skF_3', '#skF_5') | ~m1_subset_1(C_181, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_5')))) | ~v1_funct_2(C_181, u1_struct_0('#skF_3'), k2_struct_0('#skF_5')) | ~v1_funct_1(C_181) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_110, c_790])).
% 4.77/1.86  tff(c_845, plain, (![C_185]: (m1_subset_1('#skF_2'('#skF_3', '#skF_5', C_185), k1_zfmisc_1(k2_struct_0('#skF_5'))) | v5_pre_topc(C_185, '#skF_3', '#skF_5') | ~m1_subset_1(C_185, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_5')))) | ~v1_funct_2(C_185, k2_struct_0('#skF_4'), k2_struct_0('#skF_5')) | ~v1_funct_1(C_185))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_110, c_797])).
% 4.77/1.86  tff(c_852, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_struct_0('#skF_5'))) | v5_pre_topc('#skF_6', '#skF_3', '#skF_5') | ~v1_funct_2('#skF_6', k2_struct_0('#skF_4'), k2_struct_0('#skF_5')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_171, c_845])).
% 4.77/1.86  tff(c_856, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_struct_0('#skF_5'))) | v5_pre_topc('#skF_6', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_163, c_852])).
% 4.77/1.86  tff(c_857, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_70, c_856])).
% 4.77/1.86  tff(c_293, plain, (![B_88, A_89, C_90]: (k2_struct_0(B_88)=k1_xboole_0 | v3_pre_topc('#skF_2'(A_89, B_88, C_90), B_88) | v5_pre_topc(C_90, A_89, B_88) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_89), u1_struct_0(B_88)))) | ~v1_funct_2(C_90, u1_struct_0(A_89), u1_struct_0(B_88)) | ~v1_funct_1(C_90) | ~l1_pre_topc(B_88) | ~l1_pre_topc(A_89))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.77/1.86  tff(c_298, plain, (![B_88, C_90]: (k2_struct_0(B_88)=k1_xboole_0 | v3_pre_topc('#skF_2'('#skF_3', B_88, C_90), B_88) | v5_pre_topc(C_90, '#skF_3', B_88) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), u1_struct_0(B_88)))) | ~v1_funct_2(C_90, u1_struct_0('#skF_3'), u1_struct_0(B_88)) | ~v1_funct_1(C_90) | ~l1_pre_topc(B_88) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_110, c_293])).
% 4.77/1.86  tff(c_622, plain, (![B_163, C_164]: (k2_struct_0(B_163)=k1_xboole_0 | v3_pre_topc('#skF_2'('#skF_3', B_163, C_164), B_163) | v5_pre_topc(C_164, '#skF_3', B_163) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), u1_struct_0(B_163)))) | ~v1_funct_2(C_164, k2_struct_0('#skF_4'), u1_struct_0(B_163)) | ~v1_funct_1(C_164) | ~l1_pre_topc(B_163))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_110, c_298])).
% 4.77/1.86  tff(c_631, plain, (![C_164]: (k2_struct_0('#skF_5')=k1_xboole_0 | v3_pre_topc('#skF_2'('#skF_3', '#skF_5', C_164), '#skF_5') | v5_pre_topc(C_164, '#skF_3', '#skF_5') | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_5')))) | ~v1_funct_2(C_164, k2_struct_0('#skF_4'), u1_struct_0('#skF_5')) | ~v1_funct_1(C_164) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_93, c_622])).
% 4.77/1.86  tff(c_640, plain, (![C_164]: (k2_struct_0('#skF_5')=k1_xboole_0 | v3_pre_topc('#skF_2'('#skF_3', '#skF_5', C_164), '#skF_5') | v5_pre_topc(C_164, '#skF_3', '#skF_5') | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_5')))) | ~v1_funct_2(C_164, k2_struct_0('#skF_4'), k2_struct_0('#skF_5')) | ~v1_funct_1(C_164))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_93, c_631])).
% 4.77/1.86  tff(c_648, plain, (![C_166]: (v3_pre_topc('#skF_2'('#skF_3', '#skF_5', C_166), '#skF_5') | v5_pre_topc(C_166, '#skF_3', '#skF_5') | ~m1_subset_1(C_166, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_5')))) | ~v1_funct_2(C_166, k2_struct_0('#skF_4'), k2_struct_0('#skF_5')) | ~v1_funct_1(C_166))), inference(negUnitSimplification, [status(thm)], [c_514, c_640])).
% 4.77/1.86  tff(c_655, plain, (v3_pre_topc('#skF_2'('#skF_3', '#skF_5', '#skF_6'), '#skF_5') | v5_pre_topc('#skF_6', '#skF_3', '#skF_5') | ~v1_funct_2('#skF_6', k2_struct_0('#skF_4'), k2_struct_0('#skF_5')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_171, c_648])).
% 4.77/1.86  tff(c_659, plain, (v3_pre_topc('#skF_2'('#skF_3', '#skF_5', '#skF_6'), '#skF_5') | v5_pre_topc('#skF_6', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_163, c_655])).
% 4.77/1.86  tff(c_660, plain, (v3_pre_topc('#skF_2'('#skF_3', '#skF_5', '#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_70, c_659])).
% 4.77/1.86  tff(c_48, plain, (r1_tarski(u1_pre_topc('#skF_4'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.77/1.86  tff(c_42, plain, (v5_pre_topc('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.77/1.86  tff(c_1032, plain, (![B_206, A_207, C_208, D_209]: (k2_struct_0(B_206)=k1_xboole_0 | v3_pre_topc(k8_relset_1(u1_struct_0(A_207), u1_struct_0(B_206), C_208, D_209), A_207) | ~v3_pre_topc(D_209, B_206) | ~m1_subset_1(D_209, k1_zfmisc_1(u1_struct_0(B_206))) | ~v5_pre_topc(C_208, A_207, B_206) | ~m1_subset_1(C_208, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_207), u1_struct_0(B_206)))) | ~v1_funct_2(C_208, u1_struct_0(A_207), u1_struct_0(B_206)) | ~v1_funct_1(C_208) | ~l1_pre_topc(B_206) | ~l1_pre_topc(A_207))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.77/1.86  tff(c_1047, plain, (![A_207, C_208, D_209]: (k2_struct_0('#skF_5')=k1_xboole_0 | v3_pre_topc(k8_relset_1(u1_struct_0(A_207), u1_struct_0('#skF_5'), C_208, D_209), A_207) | ~v3_pre_topc(D_209, '#skF_5') | ~m1_subset_1(D_209, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v5_pre_topc(C_208, A_207, '#skF_5') | ~m1_subset_1(C_208, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_207), k2_struct_0('#skF_5')))) | ~v1_funct_2(C_208, u1_struct_0(A_207), u1_struct_0('#skF_5')) | ~v1_funct_1(C_208) | ~l1_pre_topc('#skF_5') | ~l1_pre_topc(A_207))), inference(superposition, [status(thm), theory('equality')], [c_93, c_1032])).
% 4.77/1.86  tff(c_1062, plain, (![A_207, C_208, D_209]: (k2_struct_0('#skF_5')=k1_xboole_0 | v3_pre_topc(k8_relset_1(u1_struct_0(A_207), k2_struct_0('#skF_5'), C_208, D_209), A_207) | ~v3_pre_topc(D_209, '#skF_5') | ~m1_subset_1(D_209, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~v5_pre_topc(C_208, A_207, '#skF_5') | ~m1_subset_1(C_208, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_207), k2_struct_0('#skF_5')))) | ~v1_funct_2(C_208, u1_struct_0(A_207), k2_struct_0('#skF_5')) | ~v1_funct_1(C_208) | ~l1_pre_topc(A_207))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_93, c_93, c_93, c_1047])).
% 4.77/1.86  tff(c_1334, plain, (![A_247, C_248, D_249]: (v3_pre_topc(k8_relset_1(u1_struct_0(A_247), k2_struct_0('#skF_5'), C_248, D_249), A_247) | ~v3_pre_topc(D_249, '#skF_5') | ~m1_subset_1(D_249, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~v5_pre_topc(C_248, A_247, '#skF_5') | ~m1_subset_1(C_248, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_247), k2_struct_0('#skF_5')))) | ~v1_funct_2(C_248, u1_struct_0(A_247), k2_struct_0('#skF_5')) | ~v1_funct_1(C_248) | ~l1_pre_topc(A_247))), inference(negUnitSimplification, [status(thm)], [c_514, c_1062])).
% 4.77/1.86  tff(c_1341, plain, (![C_248, D_249]: (v3_pre_topc(k8_relset_1(u1_struct_0('#skF_4'), k2_struct_0('#skF_5'), C_248, D_249), '#skF_4') | ~v3_pre_topc(D_249, '#skF_5') | ~m1_subset_1(D_249, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~v5_pre_topc(C_248, '#skF_4', '#skF_5') | ~m1_subset_1(C_248, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_5')))) | ~v1_funct_2(C_248, u1_struct_0('#skF_4'), k2_struct_0('#skF_5')) | ~v1_funct_1(C_248) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_92, c_1334])).
% 4.77/1.86  tff(c_1415, plain, (![C_257, D_258]: (v3_pre_topc(k8_relset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_5'), C_257, D_258), '#skF_4') | ~v3_pre_topc(D_258, '#skF_5') | ~m1_subset_1(D_258, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~v5_pre_topc(C_257, '#skF_4', '#skF_5') | ~m1_subset_1(C_257, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_5')))) | ~v1_funct_2(C_257, k2_struct_0('#skF_4'), k2_struct_0('#skF_5')) | ~v1_funct_1(C_257))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_92, c_92, c_1341])).
% 4.77/1.86  tff(c_1420, plain, (![D_258]: (v3_pre_topc(k8_relset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_5'), '#skF_6', D_258), '#skF_4') | ~v3_pre_topc(D_258, '#skF_5') | ~m1_subset_1(D_258, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~v5_pre_topc('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_2('#skF_6', k2_struct_0('#skF_4'), k2_struct_0('#skF_5')) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_171, c_1415])).
% 4.77/1.86  tff(c_1425, plain, (![D_259]: (v3_pre_topc(k8_relset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_5'), '#skF_6', D_259), '#skF_4') | ~v3_pre_topc(D_259, '#skF_5') | ~m1_subset_1(D_259, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_163, c_42, c_1420])).
% 4.77/1.86  tff(c_10, plain, (![A_6, B_7, C_8, D_9]: (m1_subset_1(k8_relset_1(A_6, B_7, C_8, D_9), k1_zfmisc_1(A_6)) | ~m1_subset_1(C_8, k1_zfmisc_1(k2_zfmisc_1(A_6, B_7))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.77/1.86  tff(c_186, plain, (![B_68, A_69]: (r2_hidden(B_68, u1_pre_topc(A_69)) | ~v3_pre_topc(B_68, A_69) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.77/1.86  tff(c_196, plain, (![B_68]: (r2_hidden(B_68, u1_pre_topc('#skF_4')) | ~v3_pre_topc(B_68, '#skF_4') | ~m1_subset_1(B_68, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_92, c_186])).
% 4.77/1.86  tff(c_234, plain, (![B_73]: (r2_hidden(B_73, u1_pre_topc('#skF_4')) | ~v3_pre_topc(B_73, '#skF_4') | ~m1_subset_1(B_73, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_196])).
% 4.77/1.86  tff(c_400, plain, (![B_118, C_119, D_120]: (r2_hidden(k8_relset_1(k2_struct_0('#skF_4'), B_118, C_119, D_120), u1_pre_topc('#skF_4')) | ~v3_pre_topc(k8_relset_1(k2_struct_0('#skF_4'), B_118, C_119, D_120), '#skF_4') | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), B_118))))), inference(resolution, [status(thm)], [c_10, c_234])).
% 4.77/1.86  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.77/1.86  tff(c_407, plain, (![B_118, C_119, D_120, B_2]: (r2_hidden(k8_relset_1(k2_struct_0('#skF_4'), B_118, C_119, D_120), B_2) | ~r1_tarski(u1_pre_topc('#skF_4'), B_2) | ~v3_pre_topc(k8_relset_1(k2_struct_0('#skF_4'), B_118, C_119, D_120), '#skF_4') | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), B_118))))), inference(resolution, [status(thm)], [c_400, c_2])).
% 4.77/1.86  tff(c_1431, plain, (![D_259, B_2]: (r2_hidden(k8_relset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_5'), '#skF_6', D_259), B_2) | ~r1_tarski(u1_pre_topc('#skF_4'), B_2) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_5')))) | ~v3_pre_topc(D_259, '#skF_5') | ~m1_subset_1(D_259, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_1425, c_407])).
% 4.77/1.86  tff(c_1438, plain, (![D_260, B_261]: (r2_hidden(k8_relset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_5'), '#skF_6', D_260), B_261) | ~r1_tarski(u1_pre_topc('#skF_4'), B_261) | ~v3_pre_topc(D_260, '#skF_5') | ~m1_subset_1(D_260, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_171, c_1431])).
% 4.77/1.86  tff(c_213, plain, (![B_71, A_72]: (v3_pre_topc(B_71, A_72) | ~r2_hidden(B_71, u1_pre_topc(A_72)) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.77/1.86  tff(c_220, plain, (![B_71]: (v3_pre_topc(B_71, '#skF_3') | ~r2_hidden(B_71, u1_pre_topc('#skF_3')) | ~m1_subset_1(B_71, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_110, c_213])).
% 4.77/1.86  tff(c_258, plain, (![B_77]: (v3_pre_topc(B_77, '#skF_3') | ~r2_hidden(B_77, u1_pre_topc('#skF_3')) | ~m1_subset_1(B_77, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_220])).
% 4.77/1.86  tff(c_263, plain, (![B_7, C_8, D_9]: (v3_pre_topc(k8_relset_1(k2_struct_0('#skF_4'), B_7, C_8, D_9), '#skF_3') | ~r2_hidden(k8_relset_1(k2_struct_0('#skF_4'), B_7, C_8, D_9), u1_pre_topc('#skF_3')) | ~m1_subset_1(C_8, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), B_7))))), inference(resolution, [status(thm)], [c_10, c_258])).
% 4.77/1.86  tff(c_1442, plain, (![D_260]: (v3_pre_topc(k8_relset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_5'), '#skF_6', D_260), '#skF_3') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_5')))) | ~r1_tarski(u1_pre_topc('#skF_4'), u1_pre_topc('#skF_3')) | ~v3_pre_topc(D_260, '#skF_5') | ~m1_subset_1(D_260, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_1438, c_263])).
% 4.77/1.86  tff(c_1461, plain, (![D_264]: (v3_pre_topc(k8_relset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_5'), '#skF_6', D_264), '#skF_3') | ~v3_pre_topc(D_264, '#skF_5') | ~m1_subset_1(D_264, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_171, c_1442])).
% 4.77/1.86  tff(c_811, plain, (![B_182, A_183, C_184]: (k2_struct_0(B_182)=k1_xboole_0 | ~v3_pre_topc(k8_relset_1(u1_struct_0(A_183), u1_struct_0(B_182), C_184, '#skF_2'(A_183, B_182, C_184)), A_183) | v5_pre_topc(C_184, A_183, B_182) | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_183), u1_struct_0(B_182)))) | ~v1_funct_2(C_184, u1_struct_0(A_183), u1_struct_0(B_182)) | ~v1_funct_1(C_184) | ~l1_pre_topc(B_182) | ~l1_pre_topc(A_183))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.77/1.86  tff(c_829, plain, (![A_183, C_184]: (k2_struct_0('#skF_5')=k1_xboole_0 | ~v3_pre_topc(k8_relset_1(u1_struct_0(A_183), k2_struct_0('#skF_5'), C_184, '#skF_2'(A_183, '#skF_5', C_184)), A_183) | v5_pre_topc(C_184, A_183, '#skF_5') | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_183), u1_struct_0('#skF_5')))) | ~v1_funct_2(C_184, u1_struct_0(A_183), u1_struct_0('#skF_5')) | ~v1_funct_1(C_184) | ~l1_pre_topc('#skF_5') | ~l1_pre_topc(A_183))), inference(superposition, [status(thm), theory('equality')], [c_93, c_811])).
% 4.77/1.86  tff(c_843, plain, (![A_183, C_184]: (k2_struct_0('#skF_5')=k1_xboole_0 | ~v3_pre_topc(k8_relset_1(u1_struct_0(A_183), k2_struct_0('#skF_5'), C_184, '#skF_2'(A_183, '#skF_5', C_184)), A_183) | v5_pre_topc(C_184, A_183, '#skF_5') | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_183), k2_struct_0('#skF_5')))) | ~v1_funct_2(C_184, u1_struct_0(A_183), k2_struct_0('#skF_5')) | ~v1_funct_1(C_184) | ~l1_pre_topc(A_183))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_93, c_93, c_829])).
% 4.77/1.86  tff(c_1116, plain, (![A_216, C_217]: (~v3_pre_topc(k8_relset_1(u1_struct_0(A_216), k2_struct_0('#skF_5'), C_217, '#skF_2'(A_216, '#skF_5', C_217)), A_216) | v5_pre_topc(C_217, A_216, '#skF_5') | ~m1_subset_1(C_217, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_216), k2_struct_0('#skF_5')))) | ~v1_funct_2(C_217, u1_struct_0(A_216), k2_struct_0('#skF_5')) | ~v1_funct_1(C_217) | ~l1_pre_topc(A_216))), inference(negUnitSimplification, [status(thm)], [c_514, c_843])).
% 4.77/1.86  tff(c_1119, plain, (![C_217]: (~v3_pre_topc(k8_relset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_5'), C_217, '#skF_2'('#skF_3', '#skF_5', C_217)), '#skF_3') | v5_pre_topc(C_217, '#skF_3', '#skF_5') | ~m1_subset_1(C_217, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), k2_struct_0('#skF_5')))) | ~v1_funct_2(C_217, u1_struct_0('#skF_3'), k2_struct_0('#skF_5')) | ~v1_funct_1(C_217) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_110, c_1116])).
% 4.77/1.86  tff(c_1127, plain, (![C_217]: (~v3_pre_topc(k8_relset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_5'), C_217, '#skF_2'('#skF_3', '#skF_5', C_217)), '#skF_3') | v5_pre_topc(C_217, '#skF_3', '#skF_5') | ~m1_subset_1(C_217, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_5')))) | ~v1_funct_2(C_217, k2_struct_0('#skF_4'), k2_struct_0('#skF_5')) | ~v1_funct_1(C_217))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_110, c_110, c_1119])).
% 4.77/1.86  tff(c_1465, plain, (v5_pre_topc('#skF_6', '#skF_3', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_5')))) | ~v1_funct_2('#skF_6', k2_struct_0('#skF_4'), k2_struct_0('#skF_5')) | ~v1_funct_1('#skF_6') | ~v3_pre_topc('#skF_2'('#skF_3', '#skF_5', '#skF_6'), '#skF_5') | ~m1_subset_1('#skF_2'('#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_1461, c_1127])).
% 4.77/1.86  tff(c_1470, plain, (v5_pre_topc('#skF_6', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_857, c_660, c_46, c_163, c_171, c_1465])).
% 4.77/1.86  tff(c_1472, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_1470])).
% 4.77/1.86  tff(c_1474, plain, (k2_struct_0('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_447])).
% 4.77/1.86  tff(c_56, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.77/1.86  tff(c_119, plain, (![A_52]: (~v1_xboole_0(u1_struct_0(A_52)) | ~l1_struct_0(A_52) | v2_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.77/1.86  tff(c_128, plain, (~v1_xboole_0(k2_struct_0('#skF_5')) | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_93, c_119])).
% 4.77/1.86  tff(c_131, plain, (~v1_xboole_0(k2_struct_0('#skF_5')) | ~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_56, c_128])).
% 4.77/1.86  tff(c_147, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_131])).
% 4.77/1.86  tff(c_150, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_18, c_147])).
% 4.77/1.86  tff(c_154, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_150])).
% 4.77/1.86  tff(c_155, plain, (~v1_xboole_0(k2_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_131])).
% 4.77/1.86  tff(c_1482, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1474, c_155])).
% 4.77/1.86  tff(c_1486, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_1482])).
% 4.77/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.77/1.86  
% 4.77/1.86  Inference rules
% 4.77/1.86  ----------------------
% 4.77/1.86  #Ref     : 0
% 4.77/1.86  #Sup     : 283
% 4.77/1.86  #Fact    : 0
% 4.77/1.86  #Define  : 0
% 4.77/1.86  #Split   : 7
% 4.77/1.86  #Chain   : 0
% 4.77/1.86  #Close   : 0
% 4.77/1.86  
% 4.77/1.86  Ordering : KBO
% 4.77/1.86  
% 4.77/1.86  Simplification rules
% 4.77/1.86  ----------------------
% 4.77/1.86  #Subsume      : 85
% 4.77/1.86  #Demod        : 613
% 4.77/1.86  #Tautology    : 23
% 4.77/1.86  #SimpNegUnit  : 51
% 4.77/1.86  #BackRed      : 13
% 4.77/1.86  
% 4.77/1.86  #Partial instantiations: 0
% 4.77/1.86  #Strategies tried      : 1
% 4.77/1.86  
% 4.77/1.86  Timing (in seconds)
% 4.77/1.86  ----------------------
% 4.77/1.86  Preprocessing        : 0.33
% 4.77/1.86  Parsing              : 0.17
% 4.77/1.86  CNF conversion       : 0.03
% 4.77/1.86  Main loop            : 0.75
% 4.77/1.86  Inferencing          : 0.24
% 4.77/1.86  Reduction            : 0.29
% 4.77/1.86  Demodulation         : 0.21
% 4.77/1.86  BG Simplification    : 0.03
% 4.77/1.86  Subsumption          : 0.14
% 4.77/1.86  Abstraction          : 0.03
% 4.77/1.86  MUC search           : 0.00
% 4.77/1.86  Cooper               : 0.00
% 4.77/1.86  Total                : 1.13
% 4.77/1.86  Index Insertion      : 0.00
% 4.77/1.86  Index Deletion       : 0.00
% 4.77/1.86  Index Matching       : 0.00
% 4.77/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
