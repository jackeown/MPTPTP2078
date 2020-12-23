%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:50 EST 2020

% Result     : Theorem 5.49s
% Output     : CNFRefutation 5.74s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 993 expanded)
%              Number of leaves         :   37 ( 363 expanded)
%              Depth                    :   18
%              Number of atoms          :  411 (4542 expanded)
%              Number of equality atoms :   33 ( 575 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_136,negated_conjecture,(
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

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_91,axiom,(
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

tff(f_66,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_41,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k8_relset_1(A,B,C,D),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relset_1)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_46,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_44,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_50,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_38,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_4'))))
    | ~ v5_pre_topc('#skF_5','#skF_2','#skF_4')
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_2'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_70,plain,(
    ~ v5_pre_topc('#skF_5','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_50,c_40,c_50,c_38])).

tff(c_58,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_18,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_76,plain,(
    ! [A_51] :
      ( u1_struct_0(A_51) = k2_struct_0(A_51)
      | ~ l1_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_81,plain,(
    ! [A_52] :
      ( u1_struct_0(A_52) = k2_struct_0(A_52)
      | ~ l1_pre_topc(A_52) ) ),
    inference(resolution,[status(thm)],[c_18,c_76])).

tff(c_92,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_81])).

tff(c_52,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_93,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_81])).

tff(c_100,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_44])).

tff(c_163,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_3'),k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_100])).

tff(c_99,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),k2_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_40])).

tff(c_169,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_99])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_173,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_169,c_6])).

tff(c_64,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_91,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_81])).

tff(c_94,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_50])).

tff(c_109,plain,(
    k2_struct_0('#skF_2') = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_94])).

tff(c_110,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_91])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_306,plain,(
    ! [B_87,A_88,C_89] :
      ( k2_struct_0(B_87) = k1_xboole_0
      | v3_pre_topc('#skF_1'(A_88,B_87,C_89),B_87)
      | v5_pre_topc(C_89,A_88,B_87)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_88),u1_struct_0(B_87))))
      | ~ v1_funct_2(C_89,u1_struct_0(A_88),u1_struct_0(B_87))
      | ~ v1_funct_1(C_89)
      | ~ l1_pre_topc(B_87)
      | ~ l1_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_318,plain,(
    ! [B_87,C_89] :
      ( k2_struct_0(B_87) = k1_xboole_0
      | v3_pre_topc('#skF_1'('#skF_3',B_87,C_89),B_87)
      | v5_pre_topc(C_89,'#skF_3',B_87)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'),u1_struct_0(B_87))))
      | ~ v1_funct_2(C_89,u1_struct_0('#skF_3'),u1_struct_0(B_87))
      | ~ v1_funct_1(C_89)
      | ~ l1_pre_topc(B_87)
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_306])).

tff(c_489,plain,(
    ! [B_112,C_113] :
      ( k2_struct_0(B_112) = k1_xboole_0
      | v3_pre_topc('#skF_1'('#skF_3',B_112,C_113),B_112)
      | v5_pre_topc(C_113,'#skF_3',B_112)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'),u1_struct_0(B_112))))
      | ~ v1_funct_2(C_113,k2_struct_0('#skF_3'),u1_struct_0(B_112))
      | ~ v1_funct_1(C_113)
      | ~ l1_pre_topc(B_112) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_92,c_318])).

tff(c_501,plain,(
    ! [C_113] :
      ( k2_struct_0('#skF_4') = k1_xboole_0
      | v3_pre_topc('#skF_1'('#skF_3','#skF_4',C_113),'#skF_4')
      | v5_pre_topc(C_113,'#skF_3','#skF_4')
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_113,k2_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_113)
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_489])).

tff(c_509,plain,(
    ! [C_113] :
      ( k2_struct_0('#skF_4') = k1_xboole_0
      | v3_pre_topc('#skF_1'('#skF_3','#skF_4',C_113),'#skF_4')
      | v5_pre_topc(C_113,'#skF_3','#skF_4')
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_113,k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(C_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_93,c_501])).

tff(c_838,plain,(
    k2_struct_0('#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_509])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_119,plain,(
    ! [A_53] :
      ( ~ v1_xboole_0(u1_struct_0(A_53))
      | ~ l1_struct_0(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_128,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_119])).

tff(c_131,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_128])).

tff(c_147,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_131])).

tff(c_150,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_147])).

tff(c_154,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_150])).

tff(c_155,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_131])).

tff(c_853,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_838,c_155])).

tff(c_857,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_853])).

tff(c_859,plain,(
    k2_struct_0('#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_509])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_702,plain,(
    ! [B_151,A_152,C_153] :
      ( k2_struct_0(B_151) = k1_xboole_0
      | m1_subset_1('#skF_1'(A_152,B_151,C_153),k1_zfmisc_1(u1_struct_0(B_151)))
      | v5_pre_topc(C_153,A_152,B_151)
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_152),u1_struct_0(B_151))))
      | ~ v1_funct_2(C_153,u1_struct_0(A_152),u1_struct_0(B_151))
      | ~ v1_funct_1(C_153)
      | ~ l1_pre_topc(B_151)
      | ~ l1_pre_topc(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2031,plain,(
    ! [B_293,A_294,A_295] :
      ( k2_struct_0(B_293) = k1_xboole_0
      | m1_subset_1('#skF_1'(A_294,B_293,A_295),k1_zfmisc_1(u1_struct_0(B_293)))
      | v5_pre_topc(A_295,A_294,B_293)
      | ~ v1_funct_2(A_295,u1_struct_0(A_294),u1_struct_0(B_293))
      | ~ v1_funct_1(A_295)
      | ~ l1_pre_topc(B_293)
      | ~ l1_pre_topc(A_294)
      | ~ r1_tarski(A_295,k2_zfmisc_1(u1_struct_0(A_294),u1_struct_0(B_293))) ) ),
    inference(resolution,[status(thm)],[c_8,c_702])).

tff(c_2049,plain,(
    ! [A_294,A_295] :
      ( k2_struct_0('#skF_4') = k1_xboole_0
      | m1_subset_1('#skF_1'(A_294,'#skF_4',A_295),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v5_pre_topc(A_295,A_294,'#skF_4')
      | ~ v1_funct_2(A_295,u1_struct_0(A_294),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(A_295)
      | ~ l1_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_294)
      | ~ r1_tarski(A_295,k2_zfmisc_1(u1_struct_0(A_294),k2_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_2031])).

tff(c_2065,plain,(
    ! [A_294,A_295] :
      ( k2_struct_0('#skF_4') = k1_xboole_0
      | m1_subset_1('#skF_1'(A_294,'#skF_4',A_295),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v5_pre_topc(A_295,A_294,'#skF_4')
      | ~ v1_funct_2(A_295,u1_struct_0(A_294),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(A_295)
      | ~ l1_pre_topc(A_294)
      | ~ r1_tarski(A_295,k2_zfmisc_1(u1_struct_0(A_294),k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_93,c_93,c_2049])).

tff(c_2067,plain,(
    ! [A_296,A_297] :
      ( m1_subset_1('#skF_1'(A_296,'#skF_4',A_297),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v5_pre_topc(A_297,A_296,'#skF_4')
      | ~ v1_funct_2(A_297,u1_struct_0(A_296),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(A_297)
      | ~ l1_pre_topc(A_296)
      | ~ r1_tarski(A_297,k2_zfmisc_1(u1_struct_0(A_296),k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_859,c_2065])).

tff(c_2078,plain,(
    ! [A_297] :
      ( m1_subset_1('#skF_1'('#skF_2','#skF_4',A_297),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v5_pre_topc(A_297,'#skF_2','#skF_4')
      | ~ v1_funct_2(A_297,u1_struct_0('#skF_2'),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(A_297)
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_297,k2_zfmisc_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_2067])).

tff(c_2093,plain,(
    ! [A_298] :
      ( m1_subset_1('#skF_1'('#skF_2','#skF_4',A_298),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v5_pre_topc(A_298,'#skF_2','#skF_4')
      | ~ v1_funct_2(A_298,k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(A_298)
      | ~ r1_tarski(A_298,k2_zfmisc_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_110,c_2078])).

tff(c_2104,plain,
    ( m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | v5_pre_topc('#skF_5','#skF_2','#skF_4')
    | ~ v1_funct_2('#skF_5',k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_173,c_2093])).

tff(c_2109,plain,
    ( m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | v5_pre_topc('#skF_5','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_163,c_2104])).

tff(c_2110,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_2109])).

tff(c_324,plain,(
    ! [A_88,C_89] :
      ( k2_struct_0('#skF_4') = k1_xboole_0
      | v3_pre_topc('#skF_1'(A_88,'#skF_4',C_89),'#skF_4')
      | v5_pre_topc(C_89,A_88,'#skF_4')
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_88),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_89,u1_struct_0(A_88),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_89)
      | ~ l1_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_88) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_306])).

tff(c_338,plain,(
    ! [A_88,C_89] :
      ( k2_struct_0('#skF_4') = k1_xboole_0
      | v3_pre_topc('#skF_1'(A_88,'#skF_4',C_89),'#skF_4')
      | v5_pre_topc(C_89,A_88,'#skF_4')
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_88),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_89,u1_struct_0(A_88),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(C_89)
      | ~ l1_pre_topc(A_88) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_93,c_324])).

tff(c_940,plain,(
    ! [A_181,C_182] :
      ( v3_pre_topc('#skF_1'(A_181,'#skF_4',C_182),'#skF_4')
      | v5_pre_topc(C_182,A_181,'#skF_4')
      | ~ m1_subset_1(C_182,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_181),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_182,u1_struct_0(A_181),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(C_182)
      | ~ l1_pre_topc(A_181) ) ),
    inference(negUnitSimplification,[status(thm)],[c_859,c_338])).

tff(c_951,plain,(
    ! [C_182] :
      ( v3_pre_topc('#skF_1'('#skF_2','#skF_4',C_182),'#skF_4')
      | v5_pre_topc(C_182,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_182,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_182,u1_struct_0('#skF_2'),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(C_182)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_940])).

tff(c_966,plain,(
    ! [C_183] :
      ( v3_pre_topc('#skF_1'('#skF_2','#skF_4',C_183),'#skF_4')
      | v5_pre_topc(C_183,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_183,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_183,k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(C_183) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_110,c_951])).

tff(c_973,plain,
    ( v3_pre_topc('#skF_1'('#skF_2','#skF_4','#skF_5'),'#skF_4')
    | v5_pre_topc('#skF_5','#skF_2','#skF_4')
    | ~ v1_funct_2('#skF_5',k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_169,c_966])).

tff(c_981,plain,
    ( v3_pre_topc('#skF_1'('#skF_2','#skF_4','#skF_5'),'#skF_4')
    | v5_pre_topc('#skF_5','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_163,c_973])).

tff(c_982,plain,(
    v3_pre_topc('#skF_1'('#skF_2','#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_981])).

tff(c_48,plain,(
    r1_tarski(u1_pre_topc('#skF_3'),u1_pre_topc('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_42,plain,(
    v5_pre_topc('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1313,plain,(
    ! [B_232,A_233,C_234,D_235] :
      ( k2_struct_0(B_232) = k1_xboole_0
      | v3_pre_topc(k8_relset_1(u1_struct_0(A_233),u1_struct_0(B_232),C_234,D_235),A_233)
      | ~ v3_pre_topc(D_235,B_232)
      | ~ m1_subset_1(D_235,k1_zfmisc_1(u1_struct_0(B_232)))
      | ~ v5_pre_topc(C_234,A_233,B_232)
      | ~ m1_subset_1(C_234,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_233),u1_struct_0(B_232))))
      | ~ v1_funct_2(C_234,u1_struct_0(A_233),u1_struct_0(B_232))
      | ~ v1_funct_1(C_234)
      | ~ l1_pre_topc(B_232)
      | ~ l1_pre_topc(A_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2260,plain,(
    ! [B_310,A_311,A_312,D_313] :
      ( k2_struct_0(B_310) = k1_xboole_0
      | v3_pre_topc(k8_relset_1(u1_struct_0(A_311),u1_struct_0(B_310),A_312,D_313),A_311)
      | ~ v3_pre_topc(D_313,B_310)
      | ~ m1_subset_1(D_313,k1_zfmisc_1(u1_struct_0(B_310)))
      | ~ v5_pre_topc(A_312,A_311,B_310)
      | ~ v1_funct_2(A_312,u1_struct_0(A_311),u1_struct_0(B_310))
      | ~ v1_funct_1(A_312)
      | ~ l1_pre_topc(B_310)
      | ~ l1_pre_topc(A_311)
      | ~ r1_tarski(A_312,k2_zfmisc_1(u1_struct_0(A_311),u1_struct_0(B_310))) ) ),
    inference(resolution,[status(thm)],[c_8,c_1313])).

tff(c_2290,plain,(
    ! [A_311,A_312,D_313] :
      ( k2_struct_0('#skF_4') = k1_xboole_0
      | v3_pre_topc(k8_relset_1(u1_struct_0(A_311),k2_struct_0('#skF_4'),A_312,D_313),A_311)
      | ~ v3_pre_topc(D_313,'#skF_4')
      | ~ m1_subset_1(D_313,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v5_pre_topc(A_312,A_311,'#skF_4')
      | ~ v1_funct_2(A_312,u1_struct_0(A_311),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(A_312)
      | ~ l1_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_311)
      | ~ r1_tarski(A_312,k2_zfmisc_1(u1_struct_0(A_311),u1_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_2260])).

tff(c_2308,plain,(
    ! [A_311,A_312,D_313] :
      ( k2_struct_0('#skF_4') = k1_xboole_0
      | v3_pre_topc(k8_relset_1(u1_struct_0(A_311),k2_struct_0('#skF_4'),A_312,D_313),A_311)
      | ~ v3_pre_topc(D_313,'#skF_4')
      | ~ m1_subset_1(D_313,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ v5_pre_topc(A_312,A_311,'#skF_4')
      | ~ v1_funct_2(A_312,u1_struct_0(A_311),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(A_312)
      | ~ l1_pre_topc(A_311)
      | ~ r1_tarski(A_312,k2_zfmisc_1(u1_struct_0(A_311),k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_52,c_93,c_93,c_2290])).

tff(c_2755,plain,(
    ! [A_367,A_368,D_369] :
      ( v3_pre_topc(k8_relset_1(u1_struct_0(A_367),k2_struct_0('#skF_4'),A_368,D_369),A_367)
      | ~ v3_pre_topc(D_369,'#skF_4')
      | ~ m1_subset_1(D_369,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ v5_pre_topc(A_368,A_367,'#skF_4')
      | ~ v1_funct_2(A_368,u1_struct_0(A_367),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(A_368)
      | ~ l1_pre_topc(A_367)
      | ~ r1_tarski(A_368,k2_zfmisc_1(u1_struct_0(A_367),k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_859,c_2308])).

tff(c_2769,plain,(
    ! [A_368,D_369] :
      ( v3_pre_topc(k8_relset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'),A_368,D_369),'#skF_3')
      | ~ v3_pre_topc(D_369,'#skF_4')
      | ~ m1_subset_1(D_369,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ v5_pre_topc(A_368,'#skF_3','#skF_4')
      | ~ v1_funct_2(A_368,u1_struct_0('#skF_3'),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(A_368)
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_368,k2_zfmisc_1(u1_struct_0('#skF_3'),k2_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_2755])).

tff(c_2800,plain,(
    ! [A_372,D_373] :
      ( v3_pre_topc(k8_relset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'),A_372,D_373),'#skF_3')
      | ~ v3_pre_topc(D_373,'#skF_4')
      | ~ m1_subset_1(D_373,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ v5_pre_topc(A_372,'#skF_3','#skF_4')
      | ~ v1_funct_2(A_372,k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(A_372)
      | ~ r1_tarski(A_372,k2_zfmisc_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_58,c_92,c_2769])).

tff(c_175,plain,(
    ! [A_61,B_62,C_63,D_64] :
      ( m1_subset_1(k8_relset_1(A_61,B_62,C_63,D_64),k1_zfmisc_1(A_61))
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_180,plain,(
    ! [A_65,B_66,C_67,D_68] :
      ( r1_tarski(k8_relset_1(A_65,B_66,C_67,D_68),A_65)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(resolution,[status(thm)],[c_175,c_6])).

tff(c_190,plain,(
    ! [D_68] : r1_tarski(k8_relset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'),'#skF_5',D_68),k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_169,c_180])).

tff(c_194,plain,(
    ! [B_74,A_75] :
      ( r2_hidden(B_74,u1_pre_topc(A_75))
      | ~ v3_pre_topc(B_74,A_75)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_208,plain,(
    ! [B_74] :
      ( r2_hidden(B_74,u1_pre_topc('#skF_3'))
      | ~ v3_pre_topc(B_74,'#skF_3')
      | ~ m1_subset_1(B_74,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_194])).

tff(c_235,plain,(
    ! [B_78] :
      ( r2_hidden(B_78,u1_pre_topc('#skF_3'))
      | ~ v3_pre_topc(B_78,'#skF_3')
      | ~ m1_subset_1(B_78,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_208])).

tff(c_257,plain,(
    ! [A_80] :
      ( r2_hidden(A_80,u1_pre_topc('#skF_3'))
      | ~ v3_pre_topc(A_80,'#skF_3')
      | ~ r1_tarski(A_80,k2_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_8,c_235])).

tff(c_4,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_420,plain,(
    ! [A_97,A_98] :
      ( r2_hidden(A_97,A_98)
      | ~ m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(A_98))
      | ~ v3_pre_topc(A_97,'#skF_3')
      | ~ r1_tarski(A_97,k2_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_257,c_4])).

tff(c_425,plain,(
    ! [A_99,B_100] :
      ( r2_hidden(A_99,B_100)
      | ~ v3_pre_topc(A_99,'#skF_3')
      | ~ r1_tarski(A_99,k2_struct_0('#skF_3'))
      | ~ r1_tarski(u1_pre_topc('#skF_3'),B_100) ) ),
    inference(resolution,[status(thm)],[c_8,c_420])).

tff(c_432,plain,(
    ! [D_68,B_100] :
      ( r2_hidden(k8_relset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'),'#skF_5',D_68),B_100)
      | ~ v3_pre_topc(k8_relset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'),'#skF_5',D_68),'#skF_3')
      | ~ r1_tarski(u1_pre_topc('#skF_3'),B_100) ) ),
    inference(resolution,[status(thm)],[c_190,c_425])).

tff(c_2811,plain,(
    ! [D_373,B_100] :
      ( r2_hidden(k8_relset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'),'#skF_5',D_373),B_100)
      | ~ r1_tarski(u1_pre_topc('#skF_3'),B_100)
      | ~ v3_pre_topc(D_373,'#skF_4')
      | ~ m1_subset_1(D_373,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ v5_pre_topc('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_2('#skF_5',k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_5')
      | ~ r1_tarski('#skF_5',k2_zfmisc_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_2800,c_432])).

tff(c_2818,plain,(
    ! [D_374,B_375] :
      ( r2_hidden(k8_relset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'),'#skF_5',D_374),B_375)
      | ~ r1_tarski(u1_pre_topc('#skF_3'),B_375)
      | ~ v3_pre_topc(D_374,'#skF_4')
      | ~ m1_subset_1(D_374,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_46,c_163,c_42,c_2811])).

tff(c_10,plain,(
    ! [A_7,B_8,C_9,D_10] :
      ( m1_subset_1(k8_relset_1(A_7,B_8,C_9,D_10),k1_zfmisc_1(A_7))
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_269,plain,(
    ! [B_84,A_85] :
      ( v3_pre_topc(B_84,A_85)
      | ~ r2_hidden(B_84,u1_pre_topc(A_85))
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_280,plain,(
    ! [B_84] :
      ( v3_pre_topc(B_84,'#skF_2')
      | ~ r2_hidden(B_84,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_84,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_269])).

tff(c_295,plain,(
    ! [B_86] :
      ( v3_pre_topc(B_86,'#skF_2')
      | ~ r2_hidden(B_86,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_86,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_280])).

tff(c_304,plain,(
    ! [B_8,C_9,D_10] :
      ( v3_pre_topc(k8_relset_1(k2_struct_0('#skF_3'),B_8,C_9,D_10),'#skF_2')
      | ~ r2_hidden(k8_relset_1(k2_struct_0('#skF_3'),B_8,C_9,D_10),u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'),B_8))) ) ),
    inference(resolution,[status(thm)],[c_10,c_295])).

tff(c_2826,plain,(
    ! [D_374] :
      ( v3_pre_topc(k8_relset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'),'#skF_5',D_374),'#skF_2')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))))
      | ~ r1_tarski(u1_pre_topc('#skF_3'),u1_pre_topc('#skF_2'))
      | ~ v3_pre_topc(D_374,'#skF_4')
      | ~ m1_subset_1(D_374,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_2818,c_304])).

tff(c_2921,plain,(
    ! [D_381] :
      ( v3_pre_topc(k8_relset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'),'#skF_5',D_381),'#skF_2')
      | ~ v3_pre_topc(D_381,'#skF_4')
      | ~ m1_subset_1(D_381,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_169,c_2826])).

tff(c_1024,plain,(
    ! [B_187,A_188,C_189] :
      ( k2_struct_0(B_187) = k1_xboole_0
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(A_188),u1_struct_0(B_187),C_189,'#skF_1'(A_188,B_187,C_189)),A_188)
      | v5_pre_topc(C_189,A_188,B_187)
      | ~ m1_subset_1(C_189,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_188),u1_struct_0(B_187))))
      | ~ v1_funct_2(C_189,u1_struct_0(A_188),u1_struct_0(B_187))
      | ~ v1_funct_1(C_189)
      | ~ l1_pre_topc(B_187)
      | ~ l1_pre_topc(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1042,plain,(
    ! [A_188,C_189] :
      ( k2_struct_0('#skF_4') = k1_xboole_0
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(A_188),k2_struct_0('#skF_4'),C_189,'#skF_1'(A_188,'#skF_4',C_189)),A_188)
      | v5_pre_topc(C_189,A_188,'#skF_4')
      | ~ m1_subset_1(C_189,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_188),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_189,u1_struct_0(A_188),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_189)
      | ~ l1_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_188) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_1024])).

tff(c_1056,plain,(
    ! [A_188,C_189] :
      ( k2_struct_0('#skF_4') = k1_xboole_0
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(A_188),k2_struct_0('#skF_4'),C_189,'#skF_1'(A_188,'#skF_4',C_189)),A_188)
      | v5_pre_topc(C_189,A_188,'#skF_4')
      | ~ m1_subset_1(C_189,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_188),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_189,u1_struct_0(A_188),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(C_189)
      | ~ l1_pre_topc(A_188) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_93,c_93,c_1042])).

tff(c_2519,plain,(
    ! [A_336,C_337] :
      ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(A_336),k2_struct_0('#skF_4'),C_337,'#skF_1'(A_336,'#skF_4',C_337)),A_336)
      | v5_pre_topc(C_337,A_336,'#skF_4')
      | ~ m1_subset_1(C_337,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_336),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_337,u1_struct_0(A_336),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(C_337)
      | ~ l1_pre_topc(A_336) ) ),
    inference(negUnitSimplification,[status(thm)],[c_859,c_1056])).

tff(c_2522,plain,(
    ! [C_337] :
      ( ~ v3_pre_topc(k8_relset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'),C_337,'#skF_1'('#skF_2','#skF_4',C_337)),'#skF_2')
      | v5_pre_topc(C_337,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_337,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_337,u1_struct_0('#skF_2'),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(C_337)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_2519])).

tff(c_2530,plain,(
    ! [C_337] :
      ( ~ v3_pre_topc(k8_relset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'),C_337,'#skF_1'('#skF_2','#skF_4',C_337)),'#skF_2')
      | v5_pre_topc(C_337,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_337,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_337,k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(C_337) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_110,c_110,c_2522])).

tff(c_2925,plain,
    ( v5_pre_topc('#skF_5','#skF_2','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_5',k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5')
    | ~ v3_pre_topc('#skF_1'('#skF_2','#skF_4','#skF_5'),'#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_2921,c_2530])).

tff(c_2934,plain,(
    v5_pre_topc('#skF_5','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2110,c_982,c_46,c_163,c_169,c_2925])).

tff(c_2936,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_2934])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:21:26 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.49/2.02  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.49/2.03  
% 5.49/2.03  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.49/2.03  %$ v5_pre_topc > v1_funct_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 5.49/2.03  
% 5.49/2.03  %Foreground sorts:
% 5.49/2.03  
% 5.49/2.03  
% 5.49/2.03  %Background operators:
% 5.49/2.03  
% 5.49/2.03  
% 5.49/2.03  %Foreground operators:
% 5.49/2.03  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.49/2.03  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.49/2.03  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 5.49/2.03  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.49/2.03  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.49/2.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.49/2.03  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.49/2.03  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 5.49/2.03  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.49/2.03  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.49/2.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.49/2.03  tff('#skF_5', type, '#skF_5': $i).
% 5.49/2.03  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.49/2.03  tff('#skF_2', type, '#skF_2': $i).
% 5.49/2.03  tff('#skF_3', type, '#skF_3': $i).
% 5.49/2.03  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.49/2.03  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.49/2.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.49/2.03  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.49/2.03  tff('#skF_4', type, '#skF_4': $i).
% 5.49/2.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.49/2.03  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 5.49/2.03  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.49/2.03  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.49/2.03  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 5.49/2.03  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.49/2.03  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.49/2.03  
% 5.74/2.06  tff(f_136, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((~v2_struct_0(C) & v2_pre_topc(C)) & l1_pre_topc(C)) => (((u1_struct_0(A) = u1_struct_0(B)) & r1_tarski(u1_pre_topc(B), u1_pre_topc(A))) => (![D]: ((((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(C))) & v5_pre_topc(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(C))))) => (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(A), u1_struct_0(C))) & v5_pre_topc(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(C)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_tmap_1)).
% 5.74/2.06  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.74/2.06  tff(f_45, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 5.74/2.06  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.74/2.06  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.74/2.06  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_struct_0(B) = k1_xboole_0) => (k2_struct_0(A) = k1_xboole_0)) => (v5_pre_topc(C, A, B) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (v3_pre_topc(D, B) => v3_pre_topc(k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D), A)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tops_2)).
% 5.74/2.06  tff(f_66, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 5.74/2.06  tff(f_41, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k8_relset_1(A, B, C, D), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relset_1)).
% 5.74/2.06  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 5.74/2.06  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 5.74/2.06  tff(c_46, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_136])).
% 5.74/2.06  tff(c_44, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_136])).
% 5.74/2.06  tff(c_50, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_136])).
% 5.74/2.06  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 5.74/2.06  tff(c_38, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_4')))) | ~v5_pre_topc('#skF_5', '#skF_2', '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_2'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_136])).
% 5.74/2.06  tff(c_70, plain, (~v5_pre_topc('#skF_5', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_50, c_40, c_50, c_38])).
% 5.74/2.06  tff(c_58, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_136])).
% 5.74/2.06  tff(c_18, plain, (![A_15]: (l1_struct_0(A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.74/2.06  tff(c_76, plain, (![A_51]: (u1_struct_0(A_51)=k2_struct_0(A_51) | ~l1_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.74/2.06  tff(c_81, plain, (![A_52]: (u1_struct_0(A_52)=k2_struct_0(A_52) | ~l1_pre_topc(A_52))), inference(resolution, [status(thm)], [c_18, c_76])).
% 5.74/2.06  tff(c_92, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_58, c_81])).
% 5.74/2.06  tff(c_52, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_136])).
% 5.74/2.06  tff(c_93, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_52, c_81])).
% 5.74/2.06  tff(c_100, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_3'), k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_44])).
% 5.74/2.06  tff(c_163, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_3'), k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_100])).
% 5.74/2.06  tff(c_99, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_40])).
% 5.74/2.06  tff(c_169, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_99])).
% 5.74/2.06  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.74/2.06  tff(c_173, plain, (r1_tarski('#skF_5', k2_zfmisc_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_169, c_6])).
% 5.74/2.06  tff(c_64, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_136])).
% 5.74/2.06  tff(c_91, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_64, c_81])).
% 5.74/2.06  tff(c_94, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_50])).
% 5.74/2.06  tff(c_109, plain, (k2_struct_0('#skF_2')=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_94])).
% 5.74/2.06  tff(c_110, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_109, c_91])).
% 5.74/2.06  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.74/2.06  tff(c_306, plain, (![B_87, A_88, C_89]: (k2_struct_0(B_87)=k1_xboole_0 | v3_pre_topc('#skF_1'(A_88, B_87, C_89), B_87) | v5_pre_topc(C_89, A_88, B_87) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_88), u1_struct_0(B_87)))) | ~v1_funct_2(C_89, u1_struct_0(A_88), u1_struct_0(B_87)) | ~v1_funct_1(C_89) | ~l1_pre_topc(B_87) | ~l1_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.74/2.06  tff(c_318, plain, (![B_87, C_89]: (k2_struct_0(B_87)=k1_xboole_0 | v3_pre_topc('#skF_1'('#skF_3', B_87, C_89), B_87) | v5_pre_topc(C_89, '#skF_3', B_87) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'), u1_struct_0(B_87)))) | ~v1_funct_2(C_89, u1_struct_0('#skF_3'), u1_struct_0(B_87)) | ~v1_funct_1(C_89) | ~l1_pre_topc(B_87) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_92, c_306])).
% 5.74/2.06  tff(c_489, plain, (![B_112, C_113]: (k2_struct_0(B_112)=k1_xboole_0 | v3_pre_topc('#skF_1'('#skF_3', B_112, C_113), B_112) | v5_pre_topc(C_113, '#skF_3', B_112) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'), u1_struct_0(B_112)))) | ~v1_funct_2(C_113, k2_struct_0('#skF_3'), u1_struct_0(B_112)) | ~v1_funct_1(C_113) | ~l1_pre_topc(B_112))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_92, c_318])).
% 5.74/2.06  tff(c_501, plain, (![C_113]: (k2_struct_0('#skF_4')=k1_xboole_0 | v3_pre_topc('#skF_1'('#skF_3', '#skF_4', C_113), '#skF_4') | v5_pre_topc(C_113, '#skF_3', '#skF_4') | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4')))) | ~v1_funct_2(C_113, k2_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1(C_113) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_93, c_489])).
% 5.74/2.06  tff(c_509, plain, (![C_113]: (k2_struct_0('#skF_4')=k1_xboole_0 | v3_pre_topc('#skF_1'('#skF_3', '#skF_4', C_113), '#skF_4') | v5_pre_topc(C_113, '#skF_3', '#skF_4') | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4')))) | ~v1_funct_2(C_113, k2_struct_0('#skF_3'), k2_struct_0('#skF_4')) | ~v1_funct_1(C_113))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_93, c_501])).
% 5.74/2.06  tff(c_838, plain, (k2_struct_0('#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_509])).
% 5.74/2.06  tff(c_56, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_136])).
% 5.74/2.06  tff(c_119, plain, (![A_53]: (~v1_xboole_0(u1_struct_0(A_53)) | ~l1_struct_0(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.74/2.06  tff(c_128, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_93, c_119])).
% 5.74/2.06  tff(c_131, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_56, c_128])).
% 5.74/2.06  tff(c_147, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_131])).
% 5.74/2.06  tff(c_150, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_18, c_147])).
% 5.74/2.06  tff(c_154, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_150])).
% 5.74/2.06  tff(c_155, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_131])).
% 5.74/2.06  tff(c_853, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_838, c_155])).
% 5.74/2.06  tff(c_857, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_853])).
% 5.74/2.06  tff(c_859, plain, (k2_struct_0('#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_509])).
% 5.74/2.06  tff(c_8, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.74/2.06  tff(c_702, plain, (![B_151, A_152, C_153]: (k2_struct_0(B_151)=k1_xboole_0 | m1_subset_1('#skF_1'(A_152, B_151, C_153), k1_zfmisc_1(u1_struct_0(B_151))) | v5_pre_topc(C_153, A_152, B_151) | ~m1_subset_1(C_153, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_152), u1_struct_0(B_151)))) | ~v1_funct_2(C_153, u1_struct_0(A_152), u1_struct_0(B_151)) | ~v1_funct_1(C_153) | ~l1_pre_topc(B_151) | ~l1_pre_topc(A_152))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.74/2.06  tff(c_2031, plain, (![B_293, A_294, A_295]: (k2_struct_0(B_293)=k1_xboole_0 | m1_subset_1('#skF_1'(A_294, B_293, A_295), k1_zfmisc_1(u1_struct_0(B_293))) | v5_pre_topc(A_295, A_294, B_293) | ~v1_funct_2(A_295, u1_struct_0(A_294), u1_struct_0(B_293)) | ~v1_funct_1(A_295) | ~l1_pre_topc(B_293) | ~l1_pre_topc(A_294) | ~r1_tarski(A_295, k2_zfmisc_1(u1_struct_0(A_294), u1_struct_0(B_293))))), inference(resolution, [status(thm)], [c_8, c_702])).
% 5.74/2.06  tff(c_2049, plain, (![A_294, A_295]: (k2_struct_0('#skF_4')=k1_xboole_0 | m1_subset_1('#skF_1'(A_294, '#skF_4', A_295), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v5_pre_topc(A_295, A_294, '#skF_4') | ~v1_funct_2(A_295, u1_struct_0(A_294), u1_struct_0('#skF_4')) | ~v1_funct_1(A_295) | ~l1_pre_topc('#skF_4') | ~l1_pre_topc(A_294) | ~r1_tarski(A_295, k2_zfmisc_1(u1_struct_0(A_294), k2_struct_0('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_93, c_2031])).
% 5.74/2.06  tff(c_2065, plain, (![A_294, A_295]: (k2_struct_0('#skF_4')=k1_xboole_0 | m1_subset_1('#skF_1'(A_294, '#skF_4', A_295), k1_zfmisc_1(k2_struct_0('#skF_4'))) | v5_pre_topc(A_295, A_294, '#skF_4') | ~v1_funct_2(A_295, u1_struct_0(A_294), k2_struct_0('#skF_4')) | ~v1_funct_1(A_295) | ~l1_pre_topc(A_294) | ~r1_tarski(A_295, k2_zfmisc_1(u1_struct_0(A_294), k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_93, c_93, c_2049])).
% 5.74/2.06  tff(c_2067, plain, (![A_296, A_297]: (m1_subset_1('#skF_1'(A_296, '#skF_4', A_297), k1_zfmisc_1(k2_struct_0('#skF_4'))) | v5_pre_topc(A_297, A_296, '#skF_4') | ~v1_funct_2(A_297, u1_struct_0(A_296), k2_struct_0('#skF_4')) | ~v1_funct_1(A_297) | ~l1_pre_topc(A_296) | ~r1_tarski(A_297, k2_zfmisc_1(u1_struct_0(A_296), k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_859, c_2065])).
% 5.74/2.06  tff(c_2078, plain, (![A_297]: (m1_subset_1('#skF_1'('#skF_2', '#skF_4', A_297), k1_zfmisc_1(k2_struct_0('#skF_4'))) | v5_pre_topc(A_297, '#skF_2', '#skF_4') | ~v1_funct_2(A_297, u1_struct_0('#skF_2'), k2_struct_0('#skF_4')) | ~v1_funct_1(A_297) | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_297, k2_zfmisc_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_110, c_2067])).
% 5.74/2.06  tff(c_2093, plain, (![A_298]: (m1_subset_1('#skF_1'('#skF_2', '#skF_4', A_298), k1_zfmisc_1(k2_struct_0('#skF_4'))) | v5_pre_topc(A_298, '#skF_2', '#skF_4') | ~v1_funct_2(A_298, k2_struct_0('#skF_3'), k2_struct_0('#skF_4')) | ~v1_funct_1(A_298) | ~r1_tarski(A_298, k2_zfmisc_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_110, c_2078])).
% 5.74/2.06  tff(c_2104, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | v5_pre_topc('#skF_5', '#skF_2', '#skF_4') | ~v1_funct_2('#skF_5', k2_struct_0('#skF_3'), k2_struct_0('#skF_4')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_173, c_2093])).
% 5.74/2.06  tff(c_2109, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | v5_pre_topc('#skF_5', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_163, c_2104])).
% 5.74/2.06  tff(c_2110, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_70, c_2109])).
% 5.74/2.06  tff(c_324, plain, (![A_88, C_89]: (k2_struct_0('#skF_4')=k1_xboole_0 | v3_pre_topc('#skF_1'(A_88, '#skF_4', C_89), '#skF_4') | v5_pre_topc(C_89, A_88, '#skF_4') | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_88), k2_struct_0('#skF_4')))) | ~v1_funct_2(C_89, u1_struct_0(A_88), u1_struct_0('#skF_4')) | ~v1_funct_1(C_89) | ~l1_pre_topc('#skF_4') | ~l1_pre_topc(A_88))), inference(superposition, [status(thm), theory('equality')], [c_93, c_306])).
% 5.74/2.06  tff(c_338, plain, (![A_88, C_89]: (k2_struct_0('#skF_4')=k1_xboole_0 | v3_pre_topc('#skF_1'(A_88, '#skF_4', C_89), '#skF_4') | v5_pre_topc(C_89, A_88, '#skF_4') | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_88), k2_struct_0('#skF_4')))) | ~v1_funct_2(C_89, u1_struct_0(A_88), k2_struct_0('#skF_4')) | ~v1_funct_1(C_89) | ~l1_pre_topc(A_88))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_93, c_324])).
% 5.74/2.06  tff(c_940, plain, (![A_181, C_182]: (v3_pre_topc('#skF_1'(A_181, '#skF_4', C_182), '#skF_4') | v5_pre_topc(C_182, A_181, '#skF_4') | ~m1_subset_1(C_182, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_181), k2_struct_0('#skF_4')))) | ~v1_funct_2(C_182, u1_struct_0(A_181), k2_struct_0('#skF_4')) | ~v1_funct_1(C_182) | ~l1_pre_topc(A_181))), inference(negUnitSimplification, [status(thm)], [c_859, c_338])).
% 5.74/2.06  tff(c_951, plain, (![C_182]: (v3_pre_topc('#skF_1'('#skF_2', '#skF_4', C_182), '#skF_4') | v5_pre_topc(C_182, '#skF_2', '#skF_4') | ~m1_subset_1(C_182, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4')))) | ~v1_funct_2(C_182, u1_struct_0('#skF_2'), k2_struct_0('#skF_4')) | ~v1_funct_1(C_182) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_110, c_940])).
% 5.74/2.06  tff(c_966, plain, (![C_183]: (v3_pre_topc('#skF_1'('#skF_2', '#skF_4', C_183), '#skF_4') | v5_pre_topc(C_183, '#skF_2', '#skF_4') | ~m1_subset_1(C_183, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4')))) | ~v1_funct_2(C_183, k2_struct_0('#skF_3'), k2_struct_0('#skF_4')) | ~v1_funct_1(C_183))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_110, c_951])).
% 5.74/2.06  tff(c_973, plain, (v3_pre_topc('#skF_1'('#skF_2', '#skF_4', '#skF_5'), '#skF_4') | v5_pre_topc('#skF_5', '#skF_2', '#skF_4') | ~v1_funct_2('#skF_5', k2_struct_0('#skF_3'), k2_struct_0('#skF_4')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_169, c_966])).
% 5.74/2.06  tff(c_981, plain, (v3_pre_topc('#skF_1'('#skF_2', '#skF_4', '#skF_5'), '#skF_4') | v5_pre_topc('#skF_5', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_163, c_973])).
% 5.74/2.06  tff(c_982, plain, (v3_pre_topc('#skF_1'('#skF_2', '#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_70, c_981])).
% 5.74/2.06  tff(c_48, plain, (r1_tarski(u1_pre_topc('#skF_3'), u1_pre_topc('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_136])).
% 5.74/2.06  tff(c_42, plain, (v5_pre_topc('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_136])).
% 5.74/2.06  tff(c_1313, plain, (![B_232, A_233, C_234, D_235]: (k2_struct_0(B_232)=k1_xboole_0 | v3_pre_topc(k8_relset_1(u1_struct_0(A_233), u1_struct_0(B_232), C_234, D_235), A_233) | ~v3_pre_topc(D_235, B_232) | ~m1_subset_1(D_235, k1_zfmisc_1(u1_struct_0(B_232))) | ~v5_pre_topc(C_234, A_233, B_232) | ~m1_subset_1(C_234, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_233), u1_struct_0(B_232)))) | ~v1_funct_2(C_234, u1_struct_0(A_233), u1_struct_0(B_232)) | ~v1_funct_1(C_234) | ~l1_pre_topc(B_232) | ~l1_pre_topc(A_233))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.74/2.06  tff(c_2260, plain, (![B_310, A_311, A_312, D_313]: (k2_struct_0(B_310)=k1_xboole_0 | v3_pre_topc(k8_relset_1(u1_struct_0(A_311), u1_struct_0(B_310), A_312, D_313), A_311) | ~v3_pre_topc(D_313, B_310) | ~m1_subset_1(D_313, k1_zfmisc_1(u1_struct_0(B_310))) | ~v5_pre_topc(A_312, A_311, B_310) | ~v1_funct_2(A_312, u1_struct_0(A_311), u1_struct_0(B_310)) | ~v1_funct_1(A_312) | ~l1_pre_topc(B_310) | ~l1_pre_topc(A_311) | ~r1_tarski(A_312, k2_zfmisc_1(u1_struct_0(A_311), u1_struct_0(B_310))))), inference(resolution, [status(thm)], [c_8, c_1313])).
% 5.74/2.06  tff(c_2290, plain, (![A_311, A_312, D_313]: (k2_struct_0('#skF_4')=k1_xboole_0 | v3_pre_topc(k8_relset_1(u1_struct_0(A_311), k2_struct_0('#skF_4'), A_312, D_313), A_311) | ~v3_pre_topc(D_313, '#skF_4') | ~m1_subset_1(D_313, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v5_pre_topc(A_312, A_311, '#skF_4') | ~v1_funct_2(A_312, u1_struct_0(A_311), u1_struct_0('#skF_4')) | ~v1_funct_1(A_312) | ~l1_pre_topc('#skF_4') | ~l1_pre_topc(A_311) | ~r1_tarski(A_312, k2_zfmisc_1(u1_struct_0(A_311), u1_struct_0('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_93, c_2260])).
% 5.74/2.06  tff(c_2308, plain, (![A_311, A_312, D_313]: (k2_struct_0('#skF_4')=k1_xboole_0 | v3_pre_topc(k8_relset_1(u1_struct_0(A_311), k2_struct_0('#skF_4'), A_312, D_313), A_311) | ~v3_pre_topc(D_313, '#skF_4') | ~m1_subset_1(D_313, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~v5_pre_topc(A_312, A_311, '#skF_4') | ~v1_funct_2(A_312, u1_struct_0(A_311), k2_struct_0('#skF_4')) | ~v1_funct_1(A_312) | ~l1_pre_topc(A_311) | ~r1_tarski(A_312, k2_zfmisc_1(u1_struct_0(A_311), k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_52, c_93, c_93, c_2290])).
% 5.74/2.06  tff(c_2755, plain, (![A_367, A_368, D_369]: (v3_pre_topc(k8_relset_1(u1_struct_0(A_367), k2_struct_0('#skF_4'), A_368, D_369), A_367) | ~v3_pre_topc(D_369, '#skF_4') | ~m1_subset_1(D_369, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~v5_pre_topc(A_368, A_367, '#skF_4') | ~v1_funct_2(A_368, u1_struct_0(A_367), k2_struct_0('#skF_4')) | ~v1_funct_1(A_368) | ~l1_pre_topc(A_367) | ~r1_tarski(A_368, k2_zfmisc_1(u1_struct_0(A_367), k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_859, c_2308])).
% 5.74/2.06  tff(c_2769, plain, (![A_368, D_369]: (v3_pre_topc(k8_relset_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'), A_368, D_369), '#skF_3') | ~v3_pre_topc(D_369, '#skF_4') | ~m1_subset_1(D_369, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~v5_pre_topc(A_368, '#skF_3', '#skF_4') | ~v1_funct_2(A_368, u1_struct_0('#skF_3'), k2_struct_0('#skF_4')) | ~v1_funct_1(A_368) | ~l1_pre_topc('#skF_3') | ~r1_tarski(A_368, k2_zfmisc_1(u1_struct_0('#skF_3'), k2_struct_0('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_92, c_2755])).
% 5.74/2.06  tff(c_2800, plain, (![A_372, D_373]: (v3_pre_topc(k8_relset_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'), A_372, D_373), '#skF_3') | ~v3_pre_topc(D_373, '#skF_4') | ~m1_subset_1(D_373, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~v5_pre_topc(A_372, '#skF_3', '#skF_4') | ~v1_funct_2(A_372, k2_struct_0('#skF_3'), k2_struct_0('#skF_4')) | ~v1_funct_1(A_372) | ~r1_tarski(A_372, k2_zfmisc_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_58, c_92, c_2769])).
% 5.74/2.06  tff(c_175, plain, (![A_61, B_62, C_63, D_64]: (m1_subset_1(k8_relset_1(A_61, B_62, C_63, D_64), k1_zfmisc_1(A_61)) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.74/2.06  tff(c_180, plain, (![A_65, B_66, C_67, D_68]: (r1_tarski(k8_relset_1(A_65, B_66, C_67, D_68), A_65) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(resolution, [status(thm)], [c_175, c_6])).
% 5.74/2.06  tff(c_190, plain, (![D_68]: (r1_tarski(k8_relset_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'), '#skF_5', D_68), k2_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_169, c_180])).
% 5.74/2.06  tff(c_194, plain, (![B_74, A_75]: (r2_hidden(B_74, u1_pre_topc(A_75)) | ~v3_pre_topc(B_74, A_75) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_pre_topc(A_75))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.74/2.06  tff(c_208, plain, (![B_74]: (r2_hidden(B_74, u1_pre_topc('#skF_3')) | ~v3_pre_topc(B_74, '#skF_3') | ~m1_subset_1(B_74, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_92, c_194])).
% 5.74/2.06  tff(c_235, plain, (![B_78]: (r2_hidden(B_78, u1_pre_topc('#skF_3')) | ~v3_pre_topc(B_78, '#skF_3') | ~m1_subset_1(B_78, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_208])).
% 5.74/2.06  tff(c_257, plain, (![A_80]: (r2_hidden(A_80, u1_pre_topc('#skF_3')) | ~v3_pre_topc(A_80, '#skF_3') | ~r1_tarski(A_80, k2_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_8, c_235])).
% 5.74/2.06  tff(c_4, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.74/2.06  tff(c_420, plain, (![A_97, A_98]: (r2_hidden(A_97, A_98) | ~m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(A_98)) | ~v3_pre_topc(A_97, '#skF_3') | ~r1_tarski(A_97, k2_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_257, c_4])).
% 5.74/2.06  tff(c_425, plain, (![A_99, B_100]: (r2_hidden(A_99, B_100) | ~v3_pre_topc(A_99, '#skF_3') | ~r1_tarski(A_99, k2_struct_0('#skF_3')) | ~r1_tarski(u1_pre_topc('#skF_3'), B_100))), inference(resolution, [status(thm)], [c_8, c_420])).
% 5.74/2.06  tff(c_432, plain, (![D_68, B_100]: (r2_hidden(k8_relset_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'), '#skF_5', D_68), B_100) | ~v3_pre_topc(k8_relset_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'), '#skF_5', D_68), '#skF_3') | ~r1_tarski(u1_pre_topc('#skF_3'), B_100))), inference(resolution, [status(thm)], [c_190, c_425])).
% 5.74/2.06  tff(c_2811, plain, (![D_373, B_100]: (r2_hidden(k8_relset_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'), '#skF_5', D_373), B_100) | ~r1_tarski(u1_pre_topc('#skF_3'), B_100) | ~v3_pre_topc(D_373, '#skF_4') | ~m1_subset_1(D_373, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~v5_pre_topc('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_2('#skF_5', k2_struct_0('#skF_3'), k2_struct_0('#skF_4')) | ~v1_funct_1('#skF_5') | ~r1_tarski('#skF_5', k2_zfmisc_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_2800, c_432])).
% 5.74/2.06  tff(c_2818, plain, (![D_374, B_375]: (r2_hidden(k8_relset_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'), '#skF_5', D_374), B_375) | ~r1_tarski(u1_pre_topc('#skF_3'), B_375) | ~v3_pre_topc(D_374, '#skF_4') | ~m1_subset_1(D_374, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_46, c_163, c_42, c_2811])).
% 5.74/2.06  tff(c_10, plain, (![A_7, B_8, C_9, D_10]: (m1_subset_1(k8_relset_1(A_7, B_8, C_9, D_10), k1_zfmisc_1(A_7)) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.74/2.06  tff(c_269, plain, (![B_84, A_85]: (v3_pre_topc(B_84, A_85) | ~r2_hidden(B_84, u1_pre_topc(A_85)) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.74/2.06  tff(c_280, plain, (![B_84]: (v3_pre_topc(B_84, '#skF_2') | ~r2_hidden(B_84, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_84, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_110, c_269])).
% 5.74/2.06  tff(c_295, plain, (![B_86]: (v3_pre_topc(B_86, '#skF_2') | ~r2_hidden(B_86, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_86, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_280])).
% 5.74/2.06  tff(c_304, plain, (![B_8, C_9, D_10]: (v3_pre_topc(k8_relset_1(k2_struct_0('#skF_3'), B_8, C_9, D_10), '#skF_2') | ~r2_hidden(k8_relset_1(k2_struct_0('#skF_3'), B_8, C_9, D_10), u1_pre_topc('#skF_2')) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'), B_8))))), inference(resolution, [status(thm)], [c_10, c_295])).
% 5.74/2.06  tff(c_2826, plain, (![D_374]: (v3_pre_topc(k8_relset_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'), '#skF_5', D_374), '#skF_2') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4')))) | ~r1_tarski(u1_pre_topc('#skF_3'), u1_pre_topc('#skF_2')) | ~v3_pre_topc(D_374, '#skF_4') | ~m1_subset_1(D_374, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_2818, c_304])).
% 5.74/2.06  tff(c_2921, plain, (![D_381]: (v3_pre_topc(k8_relset_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'), '#skF_5', D_381), '#skF_2') | ~v3_pre_topc(D_381, '#skF_4') | ~m1_subset_1(D_381, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_169, c_2826])).
% 5.74/2.06  tff(c_1024, plain, (![B_187, A_188, C_189]: (k2_struct_0(B_187)=k1_xboole_0 | ~v3_pre_topc(k8_relset_1(u1_struct_0(A_188), u1_struct_0(B_187), C_189, '#skF_1'(A_188, B_187, C_189)), A_188) | v5_pre_topc(C_189, A_188, B_187) | ~m1_subset_1(C_189, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_188), u1_struct_0(B_187)))) | ~v1_funct_2(C_189, u1_struct_0(A_188), u1_struct_0(B_187)) | ~v1_funct_1(C_189) | ~l1_pre_topc(B_187) | ~l1_pre_topc(A_188))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.74/2.06  tff(c_1042, plain, (![A_188, C_189]: (k2_struct_0('#skF_4')=k1_xboole_0 | ~v3_pre_topc(k8_relset_1(u1_struct_0(A_188), k2_struct_0('#skF_4'), C_189, '#skF_1'(A_188, '#skF_4', C_189)), A_188) | v5_pre_topc(C_189, A_188, '#skF_4') | ~m1_subset_1(C_189, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_188), u1_struct_0('#skF_4')))) | ~v1_funct_2(C_189, u1_struct_0(A_188), u1_struct_0('#skF_4')) | ~v1_funct_1(C_189) | ~l1_pre_topc('#skF_4') | ~l1_pre_topc(A_188))), inference(superposition, [status(thm), theory('equality')], [c_93, c_1024])).
% 5.74/2.06  tff(c_1056, plain, (![A_188, C_189]: (k2_struct_0('#skF_4')=k1_xboole_0 | ~v3_pre_topc(k8_relset_1(u1_struct_0(A_188), k2_struct_0('#skF_4'), C_189, '#skF_1'(A_188, '#skF_4', C_189)), A_188) | v5_pre_topc(C_189, A_188, '#skF_4') | ~m1_subset_1(C_189, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_188), k2_struct_0('#skF_4')))) | ~v1_funct_2(C_189, u1_struct_0(A_188), k2_struct_0('#skF_4')) | ~v1_funct_1(C_189) | ~l1_pre_topc(A_188))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_93, c_93, c_1042])).
% 5.74/2.06  tff(c_2519, plain, (![A_336, C_337]: (~v3_pre_topc(k8_relset_1(u1_struct_0(A_336), k2_struct_0('#skF_4'), C_337, '#skF_1'(A_336, '#skF_4', C_337)), A_336) | v5_pre_topc(C_337, A_336, '#skF_4') | ~m1_subset_1(C_337, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_336), k2_struct_0('#skF_4')))) | ~v1_funct_2(C_337, u1_struct_0(A_336), k2_struct_0('#skF_4')) | ~v1_funct_1(C_337) | ~l1_pre_topc(A_336))), inference(negUnitSimplification, [status(thm)], [c_859, c_1056])).
% 5.74/2.06  tff(c_2522, plain, (![C_337]: (~v3_pre_topc(k8_relset_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'), C_337, '#skF_1'('#skF_2', '#skF_4', C_337)), '#skF_2') | v5_pre_topc(C_337, '#skF_2', '#skF_4') | ~m1_subset_1(C_337, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), k2_struct_0('#skF_4')))) | ~v1_funct_2(C_337, u1_struct_0('#skF_2'), k2_struct_0('#skF_4')) | ~v1_funct_1(C_337) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_110, c_2519])).
% 5.74/2.06  tff(c_2530, plain, (![C_337]: (~v3_pre_topc(k8_relset_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'), C_337, '#skF_1'('#skF_2', '#skF_4', C_337)), '#skF_2') | v5_pre_topc(C_337, '#skF_2', '#skF_4') | ~m1_subset_1(C_337, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4')))) | ~v1_funct_2(C_337, k2_struct_0('#skF_3'), k2_struct_0('#skF_4')) | ~v1_funct_1(C_337))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_110, c_110, c_2522])).
% 5.74/2.06  tff(c_2925, plain, (v5_pre_topc('#skF_5', '#skF_2', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4')))) | ~v1_funct_2('#skF_5', k2_struct_0('#skF_3'), k2_struct_0('#skF_4')) | ~v1_funct_1('#skF_5') | ~v3_pre_topc('#skF_1'('#skF_2', '#skF_4', '#skF_5'), '#skF_4') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_2921, c_2530])).
% 5.74/2.06  tff(c_2934, plain, (v5_pre_topc('#skF_5', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2110, c_982, c_46, c_163, c_169, c_2925])).
% 5.74/2.06  tff(c_2936, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_2934])).
% 5.74/2.06  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.74/2.06  
% 5.74/2.06  Inference rules
% 5.74/2.06  ----------------------
% 5.74/2.06  #Ref     : 0
% 5.74/2.06  #Sup     : 564
% 5.74/2.06  #Fact    : 0
% 5.74/2.06  #Define  : 0
% 5.74/2.06  #Split   : 8
% 5.74/2.06  #Chain   : 0
% 5.74/2.06  #Close   : 0
% 5.74/2.06  
% 5.74/2.06  Ordering : KBO
% 5.74/2.06  
% 5.74/2.06  Simplification rules
% 5.74/2.06  ----------------------
% 5.74/2.06  #Subsume      : 155
% 5.74/2.06  #Demod        : 1005
% 5.74/2.06  #Tautology    : 66
% 5.74/2.06  #SimpNegUnit  : 84
% 5.74/2.06  #BackRed      : 45
% 5.74/2.06  
% 5.74/2.06  #Partial instantiations: 0
% 5.74/2.06  #Strategies tried      : 1
% 5.74/2.06  
% 5.74/2.06  Timing (in seconds)
% 5.74/2.06  ----------------------
% 5.74/2.06  Preprocessing        : 0.31
% 5.74/2.06  Parsing              : 0.16
% 5.74/2.06  CNF conversion       : 0.03
% 5.74/2.06  Main loop            : 0.94
% 5.74/2.06  Inferencing          : 0.30
% 5.74/2.06  Reduction            : 0.35
% 5.74/2.06  Demodulation         : 0.25
% 5.74/2.06  BG Simplification    : 0.04
% 5.74/2.06  Subsumption          : 0.19
% 5.74/2.06  Abstraction          : 0.04
% 5.74/2.06  MUC search           : 0.00
% 5.74/2.06  Cooper               : 0.00
% 5.74/2.06  Total                : 1.31
% 5.74/2.06  Index Insertion      : 0.00
% 5.74/2.06  Index Deletion       : 0.00
% 5.74/2.06  Index Matching       : 0.00
% 5.74/2.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
