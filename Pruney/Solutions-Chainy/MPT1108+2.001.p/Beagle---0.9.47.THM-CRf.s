%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:54 EST 2020

% Result     : Theorem 37.04s
% Output     : CNFRefutation 37.69s
% Verified   : 
% Statistics : Number of formulae       :  561 (12171 expanded)
%              Number of leaves         :   54 (3906 expanded)
%              Depth                    :   20
%              Number of atoms          :  902 (30179 expanded)
%              Number of equality atoms :  321 (4143 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_pre_topc > k5_relset_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_234,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                   => ( v1_funct_1(k5_relset_1(u1_struct_0(A),u1_struct_0(B),C,D))
                      & v1_funct_2(k5_relset_1(u1_struct_0(A),u1_struct_0(B),C,D),u1_struct_0(k1_pre_topc(A,D)),u1_struct_0(B))
                      & m1_subset_1(k5_relset_1(u1_struct_0(A),u1_struct_0(B),C,D),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(A,D)),u1_struct_0(B)))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_pre_topc)).

tff(f_60,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_58,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_116,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_120,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_130,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_176,axiom,(
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

tff(f_99,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_134,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(f_138,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => m1_subset_1(k5_relset_1(A,C,D,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_relset_1)).

tff(f_103,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_126,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_202,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( k1_relset_1(A,B,C) = A
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_funct_2)).

tff(f_158,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & ~ v1_xboole_0(C)
              & v1_funct_2(C,A,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_funct_2)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_209,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => u1_struct_0(k1_pre_topc(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

tff(f_111,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_93,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_110,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_26,plain,(
    ! [A_16] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_156,plain,(
    ! [A_102,B_103] :
      ( r1_tarski(A_102,B_103)
      | ~ m1_subset_1(A_102,k1_zfmisc_1(B_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_164,plain,(
    ! [A_16] : r1_tarski(k1_xboole_0,A_16) ),
    inference(resolution,[status(thm)],[c_26,c_156])).

tff(c_22,plain,(
    ! [A_14] : k2_zfmisc_1(A_14,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_165,plain,(
    ! [A_104] : r1_tarski(k1_xboole_0,A_104) ),
    inference(resolution,[status(thm)],[c_26,c_156])).

tff(c_146,plain,(
    ! [A_100] :
      ( v1_xboole_0(A_100)
      | r2_hidden('#skF_1'(A_100),A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_50,plain,(
    ! [B_38,A_37] :
      ( ~ r1_tarski(B_38,A_37)
      | ~ r2_hidden(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_153,plain,(
    ! [A_100] :
      ( ~ r1_tarski(A_100,'#skF_1'(A_100))
      | v1_xboole_0(A_100) ) ),
    inference(resolution,[status(thm)],[c_146,c_50])).

tff(c_170,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_165,c_153])).

tff(c_100,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_1678,plain,(
    ! [C_280,A_281,B_282] :
      ( v1_relat_1(C_280)
      | ~ m1_subset_1(C_280,k1_zfmisc_1(k2_zfmisc_1(A_281,B_282))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1695,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_100,c_1678])).

tff(c_102,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_26416,plain,(
    ! [A_1210,B_1211,C_1212] :
      ( k1_relset_1(A_1210,B_1211,C_1212) = k1_relat_1(C_1212)
      | ~ m1_subset_1(C_1212,k1_zfmisc_1(k2_zfmisc_1(A_1210,B_1211))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_26444,plain,(
    k1_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_100,c_26416])).

tff(c_27984,plain,(
    ! [B_1312,A_1313,C_1314] :
      ( k1_xboole_0 = B_1312
      | k1_relset_1(A_1313,B_1312,C_1314) = A_1313
      | ~ v1_funct_2(C_1314,A_1313,B_1312)
      | ~ m1_subset_1(C_1314,k1_zfmisc_1(k2_zfmisc_1(A_1313,B_1312))) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_28001,plain,
    ( u1_struct_0('#skF_4') = k1_xboole_0
    | k1_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') = u1_struct_0('#skF_3')
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_100,c_27984])).

tff(c_28018,plain,
    ( u1_struct_0('#skF_4') = k1_xboole_0
    | u1_struct_0('#skF_3') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_26444,c_28001])).

tff(c_28025,plain,(
    u1_struct_0('#skF_3') = k1_relat_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_28018])).

tff(c_98,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_163,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_98,c_156])).

tff(c_28038,plain,(
    r1_tarski('#skF_6',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28025,c_163])).

tff(c_42,plain,(
    ! [B_33,A_32] :
      ( k1_relat_1(k7_relat_1(B_33,A_32)) = A_32
      | ~ r1_tarski(A_32,k1_relat_1(B_33))
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_28071,plain,
    ( k1_relat_1(k7_relat_1('#skF_5','#skF_6')) = '#skF_6'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_28038,c_42])).

tff(c_28083,plain,(
    k1_relat_1(k7_relat_1('#skF_5','#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1695,c_28071])).

tff(c_27079,plain,(
    ! [A_1258,B_1259,C_1260,D_1261] :
      ( k5_relset_1(A_1258,B_1259,C_1260,D_1261) = k7_relat_1(C_1260,D_1261)
      | ~ m1_subset_1(C_1260,k1_zfmisc_1(k2_zfmisc_1(A_1258,B_1259))) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_27100,plain,(
    ! [D_1261] : k5_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',D_1261) = k7_relat_1('#skF_5',D_1261) ),
    inference(resolution,[status(thm)],[c_100,c_27079])).

tff(c_27693,plain,(
    ! [A_1304,C_1305,D_1306,B_1307] :
      ( m1_subset_1(k5_relset_1(A_1304,C_1305,D_1306,B_1307),k1_zfmisc_1(k2_zfmisc_1(B_1307,C_1305)))
      | ~ m1_subset_1(D_1306,k1_zfmisc_1(k2_zfmisc_1(A_1304,C_1305))) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_27722,plain,(
    ! [D_1261] :
      ( m1_subset_1(k7_relat_1('#skF_5',D_1261),k1_zfmisc_1(k2_zfmisc_1(D_1261,u1_struct_0('#skF_4'))))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27100,c_27693])).

tff(c_27748,plain,(
    ! [D_1308] : m1_subset_1(k7_relat_1('#skF_5',D_1308),k1_zfmisc_1(k2_zfmisc_1(D_1308,u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_27722])).

tff(c_58,plain,(
    ! [A_45,B_46,C_47] :
      ( k1_relset_1(A_45,B_46,C_47) = k1_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_27789,plain,(
    ! [D_1308] : k1_relset_1(D_1308,u1_struct_0('#skF_4'),k7_relat_1('#skF_5',D_1308)) = k1_relat_1(k7_relat_1('#skF_5',D_1308)) ),
    inference(resolution,[status(thm)],[c_27748,c_58])).

tff(c_27743,plain,(
    ! [D_1261] : m1_subset_1(k7_relat_1('#skF_5',D_1261),k1_zfmisc_1(k2_zfmisc_1(D_1261,u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_27722])).

tff(c_28012,plain,(
    ! [D_1261] :
      ( u1_struct_0('#skF_4') = k1_xboole_0
      | k1_relset_1(D_1261,u1_struct_0('#skF_4'),k7_relat_1('#skF_5',D_1261)) = D_1261
      | ~ v1_funct_2(k7_relat_1('#skF_5',D_1261),D_1261,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_27743,c_27984])).

tff(c_33847,plain,(
    ! [D_1261] :
      ( u1_struct_0('#skF_4') = k1_xboole_0
      | k1_relat_1(k7_relat_1('#skF_5',D_1261)) = D_1261
      | ~ v1_funct_2(k7_relat_1('#skF_5',D_1261),D_1261,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27789,c_28012])).

tff(c_33848,plain,(
    u1_struct_0('#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_33847])).

tff(c_44,plain,(
    ! [A_34] :
      ( v1_funct_1(A_34)
      | ~ v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_181,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_170,c_44])).

tff(c_16,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_32,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(A_20,k1_zfmisc_1(B_21))
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1731,plain,(
    ! [A_286,A_287,B_288] :
      ( v1_relat_1(A_286)
      | ~ r1_tarski(A_286,k2_zfmisc_1(A_287,B_288)) ) ),
    inference(resolution,[status(thm)],[c_32,c_1678])).

tff(c_1756,plain,(
    ! [A_287,B_288] : v1_relat_1(k2_zfmisc_1(A_287,B_288)) ),
    inference(resolution,[status(thm)],[c_16,c_1731])).

tff(c_24,plain,(
    ! [B_15] : k2_zfmisc_1(k1_xboole_0,B_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_3380,plain,(
    ! [C_468,A_469,B_470] :
      ( v4_relat_1(C_468,A_469)
      | ~ m1_subset_1(C_468,k1_zfmisc_1(k2_zfmisc_1(A_469,B_470))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_3593,plain,(
    ! [A_504,A_505,B_506] :
      ( v4_relat_1(A_504,A_505)
      | ~ r1_tarski(A_504,k2_zfmisc_1(A_505,B_506)) ) ),
    inference(resolution,[status(thm)],[c_32,c_3380])).

tff(c_3627,plain,(
    ! [A_505,B_506] : v4_relat_1(k2_zfmisc_1(A_505,B_506),A_505) ),
    inference(resolution,[status(thm)],[c_16,c_3593])).

tff(c_3647,plain,(
    ! [B_514,A_515] :
      ( k7_relat_1(B_514,A_515) = B_514
      | ~ v4_relat_1(B_514,A_515)
      | ~ v1_relat_1(B_514) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_3653,plain,(
    ! [A_505,B_506] :
      ( k7_relat_1(k2_zfmisc_1(A_505,B_506),A_505) = k2_zfmisc_1(A_505,B_506)
      | ~ v1_relat_1(k2_zfmisc_1(A_505,B_506)) ) ),
    inference(resolution,[status(thm)],[c_3627,c_3647])).

tff(c_3669,plain,(
    ! [A_505,B_506] : k7_relat_1(k2_zfmisc_1(A_505,B_506),A_505) = k2_zfmisc_1(A_505,B_506) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1756,c_3653])).

tff(c_3991,plain,(
    ! [B_546,A_547] :
      ( k1_relat_1(k7_relat_1(B_546,A_547)) = A_547
      | ~ r1_tarski(A_547,k1_relat_1(B_546))
      | ~ v1_relat_1(B_546) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_4012,plain,(
    ! [B_548] :
      ( k1_relat_1(k7_relat_1(B_548,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_548) ) ),
    inference(resolution,[status(thm)],[c_164,c_3991])).

tff(c_4025,plain,(
    ! [B_506] :
      ( k1_relat_1(k2_zfmisc_1(k1_xboole_0,B_506)) = k1_xboole_0
      | ~ v1_relat_1(k2_zfmisc_1(k1_xboole_0,B_506)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3669,c_4012])).

tff(c_4033,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1756,c_24,c_4025])).

tff(c_26440,plain,(
    ! [A_1210,B_1211] : k1_relset_1(A_1210,B_1211,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_26,c_26416])).

tff(c_26446,plain,(
    ! [A_1210,B_1211] : k1_relset_1(A_1210,B_1211,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4033,c_26440])).

tff(c_28281,plain,(
    ! [C_1319,A_1320,B_1321] :
      ( v1_funct_2(C_1319,A_1320,B_1321)
      | k1_relset_1(A_1320,B_1321,C_1319) != A_1320
      | ~ m1_subset_1(C_1319,k1_zfmisc_1(k2_zfmisc_1(A_1320,B_1321)))
      | ~ v1_funct_1(C_1319) ) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_28305,plain,(
    ! [A_1320,B_1321] :
      ( v1_funct_2(k1_xboole_0,A_1320,B_1321)
      | k1_relset_1(A_1320,B_1321,k1_xboole_0) != A_1320
      | ~ v1_funct_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_26,c_28281])).

tff(c_28314,plain,(
    ! [A_1320,B_1321] :
      ( v1_funct_2(k1_xboole_0,A_1320,B_1321)
      | k1_xboole_0 != A_1320 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_26446,c_28305])).

tff(c_28469,plain,(
    ! [C_1326,A_1327,B_1328] :
      ( ~ v1_xboole_0(C_1326)
      | ~ v1_funct_2(C_1326,A_1327,B_1328)
      | ~ v1_funct_1(C_1326)
      | ~ m1_subset_1(C_1326,k1_zfmisc_1(k2_zfmisc_1(A_1327,B_1328)))
      | v1_xboole_0(B_1328)
      | v1_xboole_0(A_1327) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_28496,plain,(
    ! [A_1327,B_1328] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_funct_2(k1_xboole_0,A_1327,B_1328)
      | ~ v1_funct_1(k1_xboole_0)
      | v1_xboole_0(B_1328)
      | v1_xboole_0(A_1327) ) ),
    inference(resolution,[status(thm)],[c_26,c_28469])).

tff(c_28519,plain,(
    ! [A_1330,B_1331] :
      ( ~ v1_funct_2(k1_xboole_0,A_1330,B_1331)
      | v1_xboole_0(B_1331)
      | v1_xboole_0(A_1330) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_170,c_28496])).

tff(c_28526,plain,(
    ! [B_1321,A_1320] :
      ( v1_xboole_0(B_1321)
      | v1_xboole_0(A_1320)
      | k1_xboole_0 != A_1320 ) ),
    inference(resolution,[status(thm)],[c_28314,c_28519])).

tff(c_28532,plain,(
    ! [A_1332] :
      ( v1_xboole_0(A_1332)
      | k1_xboole_0 != A_1332 ) ),
    inference(splitLeft,[status(thm)],[c_28526])).

tff(c_194,plain,(
    ! [B_110,A_111] :
      ( v1_xboole_0(B_110)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(A_111))
      | ~ v1_xboole_0(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_208,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_100,c_194])).

tff(c_1709,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_208])).

tff(c_28035,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_5'),u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28025,c_1709])).

tff(c_28577,plain,(
    k2_zfmisc_1(k1_relat_1('#skF_5'),u1_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28532,c_28035])).

tff(c_33868,plain,(
    k2_zfmisc_1(k1_relat_1('#skF_5'),k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_33848,c_28577])).

tff(c_33903,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_33868])).

tff(c_33905,plain,(
    u1_struct_0('#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_33847])).

tff(c_28092,plain,(
    ! [B_1315,C_1316,A_1317] :
      ( k1_xboole_0 = B_1315
      | v1_funct_2(C_1316,A_1317,B_1315)
      | k1_relset_1(A_1317,B_1315,C_1316) != A_1317
      | ~ m1_subset_1(C_1316,k1_zfmisc_1(k2_zfmisc_1(A_1317,B_1315))) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_28117,plain,(
    ! [D_1261] :
      ( u1_struct_0('#skF_4') = k1_xboole_0
      | v1_funct_2(k7_relat_1('#skF_5',D_1261),D_1261,u1_struct_0('#skF_4'))
      | k1_relset_1(D_1261,u1_struct_0('#skF_4'),k7_relat_1('#skF_5',D_1261)) != D_1261 ) ),
    inference(resolution,[status(thm)],[c_27743,c_28092])).

tff(c_34196,plain,(
    ! [D_1261] :
      ( u1_struct_0('#skF_4') = k1_xboole_0
      | v1_funct_2(k7_relat_1('#skF_5',D_1261),D_1261,u1_struct_0('#skF_4'))
      | k1_relat_1(k7_relat_1('#skF_5',D_1261)) != D_1261 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27789,c_28117])).

tff(c_34198,plain,(
    ! [D_1578] :
      ( v1_funct_2(k7_relat_1('#skF_5',D_1578),D_1578,u1_struct_0('#skF_4'))
      | k1_relat_1(k7_relat_1('#skF_5',D_1578)) != D_1578 ) ),
    inference(negUnitSimplification,[status(thm)],[c_33905,c_34196])).

tff(c_26570,plain,(
    ! [A_1227,B_1228] :
      ( u1_struct_0(k1_pre_topc(A_1227,B_1228)) = B_1228
      | ~ m1_subset_1(B_1228,k1_zfmisc_1(u1_struct_0(A_1227)))
      | ~ l1_pre_topc(A_1227) ) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_26581,plain,
    ( u1_struct_0(k1_pre_topc('#skF_3','#skF_6')) = '#skF_6'
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_98,c_26570])).

tff(c_26590,plain,(
    u1_struct_0(k1_pre_topc('#skF_3','#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_26581])).

tff(c_3082,plain,(
    ! [A_431,B_432,C_433,D_434] :
      ( k5_relset_1(A_431,B_432,C_433,D_434) = k7_relat_1(C_433,D_434)
      | ~ m1_subset_1(C_433,k1_zfmisc_1(k2_zfmisc_1(A_431,B_432))) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_3100,plain,(
    ! [D_434] : k5_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',D_434) = k7_relat_1('#skF_5',D_434) ),
    inference(resolution,[status(thm)],[c_100,c_3082])).

tff(c_3228,plain,(
    ! [A_454,C_455,D_456,B_457] :
      ( m1_subset_1(k5_relset_1(A_454,C_455,D_456,B_457),k1_zfmisc_1(k2_zfmisc_1(B_457,C_455)))
      | ~ m1_subset_1(D_456,k1_zfmisc_1(k2_zfmisc_1(A_454,C_455))) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_3257,plain,(
    ! [D_434] :
      ( m1_subset_1(k7_relat_1('#skF_5',D_434),k1_zfmisc_1(k2_zfmisc_1(D_434,u1_struct_0('#skF_4'))))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3100,c_3228])).

tff(c_3278,plain,(
    ! [D_434] : m1_subset_1(k7_relat_1('#skF_5',D_434),k1_zfmisc_1(k2_zfmisc_1(D_434,u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_3257])).

tff(c_2407,plain,(
    ! [A_377,B_378] :
      ( u1_struct_0(k1_pre_topc(A_377,B_378)) = B_378
      | ~ m1_subset_1(B_378,k1_zfmisc_1(u1_struct_0(A_377)))
      | ~ l1_pre_topc(A_377) ) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_2414,plain,
    ( u1_struct_0(k1_pre_topc('#skF_3','#skF_6')) = '#skF_6'
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_98,c_2407])).

tff(c_2422,plain,(
    u1_struct_0(k1_pre_topc('#skF_3','#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_2414])).

tff(c_238,plain,(
    ! [C_118,A_119,B_120] :
      ( v1_relat_1(C_118)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_255,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_100,c_238])).

tff(c_104,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_46,plain,(
    ! [A_35,B_36] :
      ( v1_funct_1(k7_relat_1(A_35,B_36))
      | ~ v1_funct_1(A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1587,plain,(
    ! [A_266,B_267,C_268,D_269] :
      ( k5_relset_1(A_266,B_267,C_268,D_269) = k7_relat_1(C_268,D_269)
      | ~ m1_subset_1(C_268,k1_zfmisc_1(k2_zfmisc_1(A_266,B_267))) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1605,plain,(
    ! [D_269] : k5_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',D_269) = k7_relat_1('#skF_5',D_269) ),
    inference(resolution,[status(thm)],[c_100,c_1587])).

tff(c_96,plain,
    ( ~ m1_subset_1(k5_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_3','#skF_6')),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2(k5_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_6'),u1_struct_0(k1_pre_topc('#skF_3','#skF_6')),u1_struct_0('#skF_4'))
    | ~ v1_funct_1(k5_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_213,plain,(
    ~ v1_funct_1(k5_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_1630,plain,(
    ~ v1_funct_1(k7_relat_1('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1605,c_213])).

tff(c_1645,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_1630])).

tff(c_1652,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_104,c_1645])).

tff(c_1653,plain,
    ( ~ v1_funct_2(k5_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_6'),u1_struct_0(k1_pre_topc('#skF_3','#skF_6')),u1_struct_0('#skF_4'))
    | ~ m1_subset_1(k5_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_3','#skF_6')),u1_struct_0('#skF_4')))) ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_1781,plain,(
    ~ m1_subset_1(k5_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_3','#skF_6')),u1_struct_0('#skF_4')))) ),
    inference(splitLeft,[status(thm)],[c_1653])).

tff(c_2425,plain,(
    ~ m1_subset_1(k5_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_6',u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2422,c_1781])).

tff(c_3139,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_6',u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3100,c_2425])).

tff(c_3293,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3278,c_3139])).

tff(c_3294,plain,(
    ~ v1_funct_2(k5_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_6'),u1_struct_0(k1_pre_topc('#skF_3','#skF_6')),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1653])).

tff(c_26595,plain,(
    ~ v1_funct_2(k5_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_6'),'#skF_6',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26590,c_3294])).

tff(c_27244,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_5','#skF_6'),'#skF_6',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27100,c_26595])).

tff(c_34201,plain,(
    k1_relat_1(k7_relat_1('#skF_5','#skF_6')) != '#skF_6' ),
    inference(resolution,[status(thm)],[c_34198,c_27244])).

tff(c_34228,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28083,c_34201])).

tff(c_34229,plain,(
    ! [B_1321] : v1_xboole_0(B_1321) ),
    inference(splitRight,[status(thm)],[c_28526])).

tff(c_209,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_98,c_194])).

tff(c_212,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_209])).

tff(c_28036,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28025,c_212])).

tff(c_28040,plain,(
    v1_funct_2('#skF_5',k1_relat_1('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28025,c_102])).

tff(c_28039,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28025,c_100])).

tff(c_28472,plain,
    ( ~ v1_xboole_0('#skF_5')
    | ~ v1_funct_2('#skF_5',k1_relat_1('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_4'))
    | v1_xboole_0(k1_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_28039,c_28469])).

tff(c_28499,plain,
    ( ~ v1_xboole_0('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_4'))
    | v1_xboole_0(k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_28040,c_28472])).

tff(c_28500,plain,
    ( ~ v1_xboole_0('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_28036,c_28499])).

tff(c_28512,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_28500])).

tff(c_34312,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34229,c_28512])).

tff(c_34314,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_28500])).

tff(c_18,plain,(
    ! [B_13,A_12] :
      ( ~ v1_xboole_0(B_13)
      | B_13 = A_12
      | ~ v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_180,plain,(
    ! [A_12] :
      ( k1_xboole_0 = A_12
      | ~ v1_xboole_0(A_12) ) ),
    inference(resolution,[status(thm)],[c_170,c_18])).

tff(c_34351,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_34314,c_180])).

tff(c_34407,plain,(
    ! [A_16] : r1_tarski('#skF_5',A_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34351,c_164])).

tff(c_34388,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34351,c_34351,c_4033])).

tff(c_3333,plain,(
    ! [B_465,A_466] :
      ( B_465 = A_466
      | ~ r1_tarski(B_465,A_466)
      | ~ r1_tarski(A_466,B_465) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_3349,plain,
    ( u1_struct_0('#skF_3') = '#skF_6'
    | ~ r1_tarski(u1_struct_0('#skF_3'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_163,c_3333])).

tff(c_3426,plain,(
    ~ r1_tarski(u1_struct_0('#skF_3'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_3349])).

tff(c_28033,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28025,c_3426])).

tff(c_34569,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34388,c_28033])).

tff(c_34575,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34407,c_34569])).

tff(c_34576,plain,(
    u1_struct_0('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_28018])).

tff(c_3295,plain,(
    m1_subset_1(k5_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_3','#skF_6')),u1_struct_0('#skF_4')))) ),
    inference(splitRight,[status(thm)],[c_1653])).

tff(c_28,plain,(
    ! [B_19,A_17] :
      ( v1_xboole_0(B_19)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(A_17))
      | ~ v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_3753,plain,
    ( v1_xboole_0(k5_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_6'))
    | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_3','#skF_6')),u1_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_3295,c_28])).

tff(c_27050,plain,
    ( v1_xboole_0(k5_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_6'))
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_6',u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26590,c_3753])).

tff(c_27051,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_6',u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_27050])).

tff(c_34587,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_6',k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34576,c_27051])).

tff(c_34601,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_22,c_34587])).

tff(c_34603,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_6',u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_27050])).

tff(c_34636,plain,(
    k2_zfmisc_1('#skF_6',u1_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34603,c_180])).

tff(c_20,plain,(
    ! [B_15,A_14] :
      ( k1_xboole_0 = B_15
      | k1_xboole_0 = A_14
      | k2_zfmisc_1(A_14,B_15) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_34724,plain,
    ( u1_struct_0('#skF_4') = k1_xboole_0
    | k1_xboole_0 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_34636,c_20])).

tff(c_34727,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_34724])).

tff(c_34774,plain,(
    ! [A_16] : r1_tarski('#skF_6',A_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34727,c_164])).

tff(c_34777,plain,(
    ! [A_14] : k2_zfmisc_1(A_14,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34727,c_34727,c_22])).

tff(c_74,plain,(
    ! [C_62,B_61] :
      ( v1_funct_2(C_62,k1_xboole_0,B_61)
      | k1_relset_1(k1_xboole_0,B_61,C_62) != k1_xboole_0
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_26748,plain,(
    ! [C_1239,B_1240] :
      ( v1_funct_2(C_1239,k1_xboole_0,B_1240)
      | k1_relset_1(k1_xboole_0,B_1240,C_1239) != k1_xboole_0
      | ~ m1_subset_1(C_1239,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_74])).

tff(c_26757,plain,(
    ! [B_1240] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_1240)
      | k1_relset_1(k1_xboole_0,B_1240,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_26748])).

tff(c_26762,plain,(
    ! [B_1240] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_1240) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26446,c_26757])).

tff(c_34739,plain,(
    ! [B_1240] : v1_funct_2('#skF_6','#skF_6',B_1240) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34727,c_34727,c_26762])).

tff(c_80,plain,(
    ! [B_61,A_60,C_62] :
      ( k1_xboole_0 = B_61
      | k1_relset_1(A_60,B_61,C_62) = A_60
      | ~ v1_funct_2(C_62,A_60,B_61)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_35293,plain,(
    ! [B_1615,A_1616,C_1617] :
      ( B_1615 = '#skF_6'
      | k1_relset_1(A_1616,B_1615,C_1617) = A_1616
      | ~ v1_funct_2(C_1617,A_1616,B_1615)
      | ~ m1_subset_1(C_1617,k1_zfmisc_1(k2_zfmisc_1(A_1616,B_1615))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34727,c_80])).

tff(c_35317,plain,
    ( u1_struct_0('#skF_4') = '#skF_6'
    | k1_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') = u1_struct_0('#skF_3')
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_100,c_35293])).

tff(c_35325,plain,
    ( u1_struct_0('#skF_4') = '#skF_6'
    | u1_struct_0('#skF_3') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_26444,c_35317])).

tff(c_35327,plain,(
    u1_struct_0('#skF_3') = k1_relat_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_35325])).

tff(c_34639,plain,(
    ! [A_1586,B_1587,C_1588,D_1589] :
      ( k5_relset_1(A_1586,B_1587,C_1588,D_1589) = k7_relat_1(C_1588,D_1589)
      | ~ m1_subset_1(C_1588,k1_zfmisc_1(k2_zfmisc_1(A_1586,B_1587))) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_34660,plain,(
    ! [D_1589] : k5_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',D_1589) = k7_relat_1('#skF_5',D_1589) ),
    inference(resolution,[status(thm)],[c_100,c_34639])).

tff(c_35329,plain,(
    ! [D_1589] : k5_relset_1(k1_relat_1('#skF_5'),u1_struct_0('#skF_4'),'#skF_5',D_1589) = k7_relat_1('#skF_5',D_1589) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35327,c_34660])).

tff(c_34602,plain,(
    v1_xboole_0(k5_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_27050])).

tff(c_35854,plain,(
    v1_xboole_0(k5_relset_1(k1_relat_1('#skF_5'),u1_struct_0('#skF_4'),'#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35327,c_34602])).

tff(c_36369,plain,(
    v1_xboole_0(k7_relat_1('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35329,c_35854])).

tff(c_34771,plain,(
    ! [A_12] :
      ( A_12 = '#skF_6'
      | ~ v1_xboole_0(A_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34727,c_180])).

tff(c_36408,plain,(
    k7_relat_1('#skF_5','#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_36369,c_34771])).

tff(c_34783,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_5','#skF_6'),'#skF_6',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34660,c_26595])).

tff(c_36421,plain,(
    ~ v1_funct_2('#skF_6','#skF_6',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36408,c_34783])).

tff(c_36430,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34739,c_36421])).

tff(c_36431,plain,(
    u1_struct_0('#skF_4') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_35325])).

tff(c_30,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(A_20,B_21)
      | ~ m1_subset_1(A_20,k1_zfmisc_1(B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_174,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_100,c_30])).

tff(c_3347,plain,
    ( k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) = '#skF_5'
    | ~ r1_tarski(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_174,c_3333])).

tff(c_3489,plain,(
    ~ r1_tarski(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_3347])).

tff(c_36471,plain,(
    ~ r1_tarski(k2_zfmisc_1(u1_struct_0('#skF_3'),'#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36431,c_3489])).

tff(c_36480,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34774,c_34777,c_36471])).

tff(c_36481,plain,(
    u1_struct_0('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_34724])).

tff(c_36490,plain,(
    ~ r1_tarski(k2_zfmisc_1(u1_struct_0('#skF_3'),k1_xboole_0),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36481,c_3489])).

tff(c_36501,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_22,c_36490])).

tff(c_36502,plain,(
    k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3347])).

tff(c_36505,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36502,c_1709])).

tff(c_36518,plain,
    ( u1_struct_0('#skF_4') = k1_xboole_0
    | u1_struct_0('#skF_3') = k1_xboole_0
    | k1_xboole_0 != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_36502,c_20])).

tff(c_37092,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_36518])).

tff(c_3399,plain,(
    v4_relat_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_100,c_3380])).

tff(c_36564,plain,(
    ! [B_1694,A_1695] :
      ( k7_relat_1(B_1694,A_1695) = B_1694
      | ~ v4_relat_1(B_1694,A_1695)
      | ~ v1_relat_1(B_1694) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_36570,plain,
    ( k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_3399,c_36564])).

tff(c_36577,plain,(
    k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1695,c_36570])).

tff(c_69599,plain,(
    ! [A_3032,B_3033,C_3034,D_3035] :
      ( k5_relset_1(A_3032,B_3033,C_3034,D_3035) = k7_relat_1(C_3034,D_3035)
      | ~ m1_subset_1(C_3034,k1_zfmisc_1(k2_zfmisc_1(A_3032,B_3033))) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_73810,plain,(
    ! [A_3342,B_3343,A_3344,D_3345] :
      ( k5_relset_1(A_3342,B_3343,A_3344,D_3345) = k7_relat_1(A_3344,D_3345)
      | ~ r1_tarski(A_3344,k2_zfmisc_1(A_3342,B_3343)) ) ),
    inference(resolution,[status(thm)],[c_32,c_69599])).

tff(c_73995,plain,(
    ! [A_3355,D_3356] :
      ( k5_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),A_3355,D_3356) = k7_relat_1(A_3355,D_3356)
      | ~ r1_tarski(A_3355,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36502,c_73810])).

tff(c_37152,plain,(
    ! [A_1767,B_1768] :
      ( u1_struct_0(k1_pre_topc(A_1767,B_1768)) = B_1768
      | ~ m1_subset_1(B_1768,k1_zfmisc_1(u1_struct_0(A_1767)))
      | ~ l1_pre_topc(A_1767) ) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_37159,plain,
    ( u1_struct_0(k1_pre_topc('#skF_3','#skF_6')) = '#skF_6'
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_98,c_37152])).

tff(c_37167,plain,(
    u1_struct_0(k1_pre_topc('#skF_3','#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_37159])).

tff(c_37171,plain,(
    ~ v1_funct_2(k5_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_6'),'#skF_6',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37167,c_3294])).

tff(c_37059,plain,(
    ! [A_1754,B_1755,C_1756] :
      ( k1_relset_1(A_1754,B_1755,C_1756) = k1_relat_1(C_1756)
      | ~ m1_subset_1(C_1756,k1_zfmisc_1(k2_zfmisc_1(A_1754,B_1755))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_37080,plain,(
    k1_relset_1(u1_struct_0(k1_pre_topc('#skF_3','#skF_6')),u1_struct_0('#skF_4'),k5_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_6')) = k1_relat_1(k5_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_3295,c_37059])).

tff(c_69998,plain,(
    k1_relset_1('#skF_6',u1_struct_0('#skF_4'),k5_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_6')) = k1_relat_1(k5_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37167,c_37080])).

tff(c_37170,plain,(
    m1_subset_1(k5_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_6',u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37167,c_3295])).

tff(c_70266,plain,(
    ! [B_3092,C_3093,A_3094] :
      ( k1_xboole_0 = B_3092
      | v1_funct_2(C_3093,A_3094,B_3092)
      | k1_relset_1(A_3094,B_3092,C_3093) != A_3094
      | ~ m1_subset_1(C_3093,k1_zfmisc_1(k2_zfmisc_1(A_3094,B_3092))) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_70272,plain,
    ( u1_struct_0('#skF_4') = k1_xboole_0
    | v1_funct_2(k5_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_6'),'#skF_6',u1_struct_0('#skF_4'))
    | k1_relset_1('#skF_6',u1_struct_0('#skF_4'),k5_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_6')) != '#skF_6' ),
    inference(resolution,[status(thm)],[c_37170,c_70266])).

tff(c_70296,plain,
    ( u1_struct_0('#skF_4') = k1_xboole_0
    | v1_funct_2(k5_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_6'),'#skF_6',u1_struct_0('#skF_4'))
    | k1_relat_1(k5_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_6')) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69998,c_70272])).

tff(c_70297,plain,
    ( u1_struct_0('#skF_4') = k1_xboole_0
    | k1_relat_1(k5_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_6')) != '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_37171,c_70296])).

tff(c_70363,plain,(
    k1_relat_1(k5_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_6')) != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_70297])).

tff(c_74032,plain,
    ( k1_relat_1(k7_relat_1('#skF_5','#skF_6')) != '#skF_6'
    | ~ r1_tarski('#skF_5','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_73995,c_70363])).

tff(c_74087,plain,(
    k1_relat_1(k7_relat_1('#skF_5','#skF_6')) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_74032])).

tff(c_78325,plain,(
    ! [B_3522,A_3523,A_3524] :
      ( k1_xboole_0 = B_3522
      | v1_funct_2(A_3523,A_3524,B_3522)
      | k1_relset_1(A_3524,B_3522,A_3523) != A_3524
      | ~ r1_tarski(A_3523,k2_zfmisc_1(A_3524,B_3522)) ) ),
    inference(resolution,[status(thm)],[c_32,c_70266])).

tff(c_78357,plain,(
    ! [A_3523] :
      ( u1_struct_0('#skF_4') = k1_xboole_0
      | v1_funct_2(A_3523,u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | k1_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),A_3523) != u1_struct_0('#skF_3')
      | ~ r1_tarski(A_3523,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36502,c_78325])).

tff(c_78446,plain,(
    u1_struct_0('#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_78357])).

tff(c_1696,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_26,c_1678])).

tff(c_40,plain,(
    ! [B_31,A_30] :
      ( r1_tarski(k7_relat_1(B_31,A_30),B_31)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_3355,plain,(
    ! [A_467] :
      ( k1_xboole_0 = A_467
      | ~ r1_tarski(A_467,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_164,c_3333])).

tff(c_3363,plain,(
    ! [A_30] :
      ( k7_relat_1(k1_xboole_0,A_30) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_40,c_3355])).

tff(c_3375,plain,(
    ! [A_30] : k7_relat_1(k1_xboole_0,A_30) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1696,c_3363])).

tff(c_36887,plain,(
    ! [B_1740,A_1741] :
      ( k1_relat_1(k7_relat_1(B_1740,A_1741)) = A_1741
      | ~ r1_tarski(A_1741,k1_relat_1(B_1740))
      | ~ v1_relat_1(B_1740) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_36908,plain,(
    ! [B_1742] :
      ( k1_relat_1(k7_relat_1(B_1742,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_1742) ) ),
    inference(resolution,[status(thm)],[c_164,c_36887])).

tff(c_36921,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3375,c_36908])).

tff(c_36925,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1696,c_36921])).

tff(c_37079,plain,(
    ! [A_1754,B_1755] : k1_relset_1(A_1754,B_1755,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_26,c_37059])).

tff(c_37083,plain,(
    ! [A_1754,B_1755] : k1_relset_1(A_1754,B_1755,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36925,c_37079])).

tff(c_70516,plain,(
    ! [C_3103,A_3104,B_3105] :
      ( v1_funct_2(C_3103,A_3104,B_3105)
      | k1_relset_1(A_3104,B_3105,C_3103) != A_3104
      | ~ m1_subset_1(C_3103,k1_zfmisc_1(k2_zfmisc_1(A_3104,B_3105)))
      | ~ v1_funct_1(C_3103) ) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_70543,plain,(
    ! [A_3104,B_3105] :
      ( v1_funct_2(k1_xboole_0,A_3104,B_3105)
      | k1_relset_1(A_3104,B_3105,k1_xboole_0) != A_3104
      | ~ v1_funct_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_26,c_70516])).

tff(c_70554,plain,(
    ! [A_3104,B_3105] :
      ( v1_funct_2(k1_xboole_0,A_3104,B_3105)
      | k1_xboole_0 != A_3104 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_37083,c_70543])).

tff(c_71353,plain,(
    ! [C_3147,A_3148,B_3149] :
      ( ~ v1_xboole_0(C_3147)
      | ~ v1_funct_2(C_3147,A_3148,B_3149)
      | ~ v1_funct_1(C_3147)
      | ~ m1_subset_1(C_3147,k1_zfmisc_1(k2_zfmisc_1(A_3148,B_3149)))
      | v1_xboole_0(B_3149)
      | v1_xboole_0(A_3148) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_71383,plain,(
    ! [A_3148,B_3149] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_funct_2(k1_xboole_0,A_3148,B_3149)
      | ~ v1_funct_1(k1_xboole_0)
      | v1_xboole_0(B_3149)
      | v1_xboole_0(A_3148) ) ),
    inference(resolution,[status(thm)],[c_26,c_71353])).

tff(c_71398,plain,(
    ! [A_3150,B_3151] :
      ( ~ v1_funct_2(k1_xboole_0,A_3150,B_3151)
      | v1_xboole_0(B_3151)
      | v1_xboole_0(A_3150) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_170,c_71383])).

tff(c_71405,plain,(
    ! [B_3105,A_3104] :
      ( v1_xboole_0(B_3105)
      | v1_xboole_0(A_3104)
      | k1_xboole_0 != A_3104 ) ),
    inference(resolution,[status(thm)],[c_70554,c_71398])).

tff(c_71411,plain,(
    ! [A_3152] :
      ( v1_xboole_0(A_3152)
      | k1_xboole_0 != A_3152 ) ),
    inference(splitLeft,[status(thm)],[c_71405])).

tff(c_36639,plain,
    ( v1_xboole_0(k5_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_6'))
    | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_3','#skF_6')),u1_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_3295,c_28])).

tff(c_69653,plain,
    ( v1_xboole_0(k5_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_6'))
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_6',u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37167,c_36639])).

tff(c_69654,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_6',u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_69653])).

tff(c_71445,plain,(
    k2_zfmisc_1('#skF_6',u1_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_71411,c_69654])).

tff(c_78478,plain,(
    k2_zfmisc_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_78446,c_71445])).

tff(c_78502,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_78478])).

tff(c_78504,plain,(
    u1_struct_0('#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_78357])).

tff(c_71264,plain,(
    ! [A_3139,B_3140,A_3141] :
      ( k1_relset_1(A_3139,B_3140,A_3141) = k1_relat_1(A_3141)
      | ~ r1_tarski(A_3141,k2_zfmisc_1(A_3139,B_3140)) ) ),
    inference(resolution,[status(thm)],[c_32,c_37059])).

tff(c_71311,plain,(
    ! [A_3139,B_3140] : k1_relset_1(A_3139,B_3140,k2_zfmisc_1(A_3139,B_3140)) = k1_relat_1(k2_zfmisc_1(A_3139,B_3140)) ),
    inference(resolution,[status(thm)],[c_16,c_71264])).

tff(c_70190,plain,(
    ! [B_3086,A_3087,C_3088] :
      ( k1_xboole_0 = B_3086
      | k1_relset_1(A_3087,B_3086,C_3088) = A_3087
      | ~ v1_funct_2(C_3088,A_3087,B_3086)
      | ~ m1_subset_1(C_3088,k1_zfmisc_1(k2_zfmisc_1(A_3087,B_3086))) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_79549,plain,(
    ! [B_3560,A_3561,A_3562] :
      ( k1_xboole_0 = B_3560
      | k1_relset_1(A_3561,B_3560,A_3562) = A_3561
      | ~ v1_funct_2(A_3562,A_3561,B_3560)
      | ~ r1_tarski(A_3562,k2_zfmisc_1(A_3561,B_3560)) ) ),
    inference(resolution,[status(thm)],[c_32,c_70190])).

tff(c_79603,plain,(
    ! [B_3560,A_3561] :
      ( k1_xboole_0 = B_3560
      | k1_relset_1(A_3561,B_3560,k2_zfmisc_1(A_3561,B_3560)) = A_3561
      | ~ v1_funct_2(k2_zfmisc_1(A_3561,B_3560),A_3561,B_3560) ) ),
    inference(resolution,[status(thm)],[c_16,c_79549])).

tff(c_154078,plain,(
    ! [B_4289,A_4290] :
      ( k1_xboole_0 = B_4289
      | k1_relat_1(k2_zfmisc_1(A_4290,B_4289)) = A_4290
      | ~ v1_funct_2(k2_zfmisc_1(A_4290,B_4289),A_4290,B_4289) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71311,c_79603])).

tff(c_154100,plain,
    ( u1_struct_0('#skF_4') = k1_xboole_0
    | k1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))) = u1_struct_0('#skF_3')
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_36502,c_154078])).

tff(c_154120,plain,
    ( u1_struct_0('#skF_4') = k1_xboole_0
    | u1_struct_0('#skF_3') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_36502,c_154100])).

tff(c_154121,plain,(
    u1_struct_0('#skF_3') = k1_relat_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_78504,c_154120])).

tff(c_154187,plain,(
    r1_tarski('#skF_6',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154121,c_163])).

tff(c_154337,plain,
    ( k1_relat_1(k7_relat_1('#skF_5','#skF_6')) = '#skF_6'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_154187,c_42])).

tff(c_154373,plain,(
    k1_relat_1(k7_relat_1('#skF_5','#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1695,c_154337])).

tff(c_154375,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74087,c_154373])).

tff(c_154376,plain,(
    ! [B_3105] : v1_xboole_0(B_3105) ),
    inference(splitRight,[status(thm)],[c_71405])).

tff(c_154495,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_154376,c_69654])).

tff(c_154496,plain,(
    u1_struct_0('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_70297])).

tff(c_154501,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_6',k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154496,c_69654])).

tff(c_154518,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_22,c_154501])).

tff(c_154520,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_6',u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_69653])).

tff(c_154565,plain,(
    k2_zfmisc_1('#skF_6',u1_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_154520,c_180])).

tff(c_154628,plain,
    ( u1_struct_0('#skF_4') = k1_xboole_0
    | k1_xboole_0 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_154565,c_20])).

tff(c_154631,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_154628])).

tff(c_154675,plain,(
    v1_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154631,c_181])).

tff(c_154658,plain,(
    ! [A_1754,B_1755] : k1_relset_1(A_1754,B_1755,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_154631,c_154631,c_37083])).

tff(c_154681,plain,(
    ! [A_16] : m1_subset_1('#skF_6',k1_zfmisc_1(A_16)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154631,c_26])).

tff(c_155292,plain,(
    ! [C_4324,A_4325,B_4326] :
      ( v1_funct_2(C_4324,A_4325,B_4326)
      | k1_relset_1(A_4325,B_4326,C_4324) != A_4325
      | ~ m1_subset_1(C_4324,k1_zfmisc_1(k2_zfmisc_1(A_4325,B_4326)))
      | ~ v1_funct_1(C_4324) ) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_155299,plain,(
    ! [A_4325,B_4326] :
      ( v1_funct_2('#skF_6',A_4325,B_4326)
      | k1_relset_1(A_4325,B_4326,'#skF_6') != A_4325
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_154681,c_155292])).

tff(c_155611,plain,(
    ! [B_4326] : v1_funct_2('#skF_6','#skF_6',B_4326) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154675,c_154658,c_155299])).

tff(c_154679,plain,(
    ! [B_15] : k2_zfmisc_1('#skF_6',B_15) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_154631,c_154631,c_24])).

tff(c_69290,plain,(
    r1_tarski(k5_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_6'),k2_zfmisc_1('#skF_6',u1_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_37170,c_30])).

tff(c_155179,plain,(
    r1_tarski(k5_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_6'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154679,c_69290])).

tff(c_3350,plain,(
    ! [A_16] :
      ( k1_xboole_0 = A_16
      | ~ r1_tarski(A_16,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_164,c_3333])).

tff(c_155233,plain,(
    ! [A_4322] :
      ( A_4322 = '#skF_6'
      | ~ r1_tarski(A_4322,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154631,c_154631,c_3350])).

tff(c_155253,plain,(
    k5_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_155179,c_155233])).

tff(c_155901,plain,(
    ~ v1_funct_2('#skF_6','#skF_6',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155253,c_37171])).

tff(c_155912,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_155611,c_155901])).

tff(c_155913,plain,(
    u1_struct_0('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_154628])).

tff(c_155923,plain,(
    k2_zfmisc_1(u1_struct_0('#skF_3'),k1_xboole_0) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_155913,c_36502])).

tff(c_36758,plain,(
    ! [A_1721,A_1722,B_1723] :
      ( v4_relat_1(A_1721,A_1722)
      | ~ r1_tarski(A_1721,k2_zfmisc_1(A_1722,B_1723)) ) ),
    inference(resolution,[status(thm)],[c_32,c_3380])).

tff(c_36812,plain,(
    ! [A_1729,B_1730] : v4_relat_1(k2_zfmisc_1(A_1729,B_1730),A_1729) ),
    inference(resolution,[status(thm)],[c_16,c_36758])).

tff(c_38,plain,(
    ! [B_29,A_28] :
      ( k7_relat_1(B_29,A_28) = B_29
      | ~ v4_relat_1(B_29,A_28)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_36815,plain,(
    ! [A_1729,B_1730] :
      ( k7_relat_1(k2_zfmisc_1(A_1729,B_1730),A_1729) = k2_zfmisc_1(A_1729,B_1730)
      | ~ v1_relat_1(k2_zfmisc_1(A_1729,B_1730)) ) ),
    inference(resolution,[status(thm)],[c_36812,c_38])).

tff(c_36827,plain,(
    ! [A_1729,B_1730] : k7_relat_1(k2_zfmisc_1(A_1729,B_1730),A_1729) = k2_zfmisc_1(A_1729,B_1730) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1756,c_36815])).

tff(c_155973,plain,(
    k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k2_zfmisc_1(u1_struct_0('#skF_3'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_155923,c_36827])).

tff(c_156016,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_36577,c_155973])).

tff(c_156018,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37092,c_156016])).

tff(c_156020,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_36518])).

tff(c_156039,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_156020,c_170])).

tff(c_156048,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36505,c_156039])).

tff(c_156049,plain,(
    u1_struct_0('#skF_3') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_3349])).

tff(c_156058,plain,(
    v1_funct_2('#skF_5','#skF_6',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156049,c_102])).

tff(c_156051,plain,(
    v4_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_156049,c_3399])).

tff(c_156259,plain,(
    ! [B_4417,A_4418] :
      ( k7_relat_1(B_4417,A_4418) = B_4417
      | ~ v4_relat_1(B_4417,A_4418)
      | ~ v1_relat_1(B_4417) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_156274,plain,
    ( k7_relat_1('#skF_5','#skF_6') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_156051,c_156259])).

tff(c_156286,plain,(
    k7_relat_1('#skF_5','#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1695,c_156274])).

tff(c_156057,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_6',u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156049,c_100])).

tff(c_157491,plain,(
    ! [A_4521,B_4522,C_4523,D_4524] :
      ( k5_relset_1(A_4521,B_4522,C_4523,D_4524) = k7_relat_1(C_4523,D_4524)
      | ~ m1_subset_1(C_4523,k1_zfmisc_1(k2_zfmisc_1(A_4521,B_4522))) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_157508,plain,(
    ! [D_4524] : k5_relset_1('#skF_6',u1_struct_0('#skF_4'),'#skF_5',D_4524) = k7_relat_1('#skF_5',D_4524) ),
    inference(resolution,[status(thm)],[c_156057,c_157491])).

tff(c_156059,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156049,c_98])).

tff(c_156971,plain,(
    ! [A_4477,B_4478] :
      ( u1_struct_0(k1_pre_topc(A_4477,B_4478)) = B_4478
      | ~ m1_subset_1(B_4478,k1_zfmisc_1(u1_struct_0(A_4477)))
      | ~ l1_pre_topc(A_4477) ) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_156978,plain,(
    ! [B_4478] :
      ( u1_struct_0(k1_pre_topc('#skF_3',B_4478)) = B_4478
      | ~ m1_subset_1(B_4478,k1_zfmisc_1('#skF_6'))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_156049,c_156971])).

tff(c_157208,plain,(
    ! [B_4495] :
      ( u1_struct_0(k1_pre_topc('#skF_3',B_4495)) = B_4495
      | ~ m1_subset_1(B_4495,k1_zfmisc_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_156978])).

tff(c_157225,plain,(
    u1_struct_0(k1_pre_topc('#skF_3','#skF_6')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_156059,c_157208])).

tff(c_156586,plain,(
    ~ v1_funct_2(k5_relset_1('#skF_6',u1_struct_0('#skF_4'),'#skF_5','#skF_6'),u1_struct_0(k1_pre_topc('#skF_3','#skF_6')),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156049,c_3294])).

tff(c_157229,plain,(
    ~ v1_funct_2(k5_relset_1('#skF_6',u1_struct_0('#skF_4'),'#skF_5','#skF_6'),'#skF_6',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157225,c_156586])).

tff(c_157521,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_5','#skF_6'),'#skF_6',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157508,c_157229])).

tff(c_157527,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_156058,c_156286,c_157521])).

tff(c_157528,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_208])).

tff(c_157538,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_157528,c_180])).

tff(c_70,plain,(
    ! [A_60] :
      ( v1_funct_2(k1_xboole_0,A_60,k1_xboole_0)
      | k1_xboole_0 = A_60
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_60,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_112,plain,(
    ! [A_60] :
      ( v1_funct_2(k1_xboole_0,A_60,k1_xboole_0)
      | k1_xboole_0 = A_60 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_70])).

tff(c_163716,plain,(
    ! [A_60] :
      ( v1_funct_2('#skF_5',A_60,'#skF_5')
      | A_60 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157538,c_157538,c_157538,c_112])).

tff(c_163718,plain,(
    ! [A_14] : k2_zfmisc_1(A_14,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_157538,c_157538,c_22])).

tff(c_163715,plain,(
    ! [A_16] : r1_tarski('#skF_5',A_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157538,c_164])).

tff(c_157529,plain,(
    v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_208])).

tff(c_163747,plain,(
    ! [A_5099] :
      ( A_5099 = '#skF_5'
      | ~ v1_xboole_0(A_5099) ) ),
    inference(resolution,[status(thm)],[c_157528,c_18])).

tff(c_163754,plain,(
    k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_157529,c_163747])).

tff(c_163945,plain,(
    ! [B_5118,A_5119] :
      ( B_5118 = '#skF_5'
      | A_5119 = '#skF_5'
      | k2_zfmisc_1(A_5119,B_5118) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157538,c_157538,c_157538,c_20])).

tff(c_163955,plain,
    ( u1_struct_0('#skF_4') = '#skF_5'
    | u1_struct_0('#skF_3') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_163754,c_163945])).

tff(c_163960,plain,(
    u1_struct_0('#skF_3') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_163955])).

tff(c_163850,plain,(
    ! [B_5109,A_5110] :
      ( B_5109 = A_5110
      | ~ r1_tarski(B_5109,A_5110)
      | ~ r1_tarski(A_5110,B_5109) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_163861,plain,
    ( u1_struct_0('#skF_3') = '#skF_6'
    | ~ r1_tarski(u1_struct_0('#skF_3'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_163,c_163850])).

tff(c_163910,plain,(
    ~ r1_tarski(u1_struct_0('#skF_3'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_163861])).

tff(c_163962,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_163960,c_163910])).

tff(c_163971,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_163715,c_163962])).

tff(c_163972,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_163955])).

tff(c_157548,plain,(
    ! [A_16] : r1_tarski('#skF_5',A_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157538,c_164])).

tff(c_157588,plain,(
    ! [B_4531,A_4532] :
      ( B_4531 = A_4532
      | ~ r1_tarski(B_4531,A_4532)
      | ~ r1_tarski(A_4532,B_4531) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_157672,plain,(
    ! [A_4537] :
      ( A_4537 = '#skF_5'
      | ~ r1_tarski(A_4537,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_157548,c_157588])).

tff(c_157680,plain,(
    ! [A_30] :
      ( k7_relat_1('#skF_5',A_30) = '#skF_5'
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_157672])).

tff(c_157689,plain,(
    ! [A_30] : k7_relat_1('#skF_5',A_30) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1695,c_157680])).

tff(c_157552,plain,(
    ! [A_16] : m1_subset_1('#skF_5',k1_zfmisc_1(A_16)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157538,c_26])).

tff(c_163683,plain,(
    ! [A_5094,B_5095,C_5096,D_5097] :
      ( k5_relset_1(A_5094,B_5095,C_5096,D_5097) = k7_relat_1(C_5096,D_5097)
      | ~ m1_subset_1(C_5096,k1_zfmisc_1(k2_zfmisc_1(A_5094,B_5095))) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_163689,plain,(
    ! [A_5094,B_5095,D_5097] : k5_relset_1(A_5094,B_5095,'#skF_5',D_5097) = k7_relat_1('#skF_5',D_5097) ),
    inference(resolution,[status(thm)],[c_157552,c_163683])).

tff(c_163699,plain,(
    ! [A_5094,B_5095,D_5097] : k5_relset_1(A_5094,B_5095,'#skF_5',D_5097) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_157689,c_163689])).

tff(c_161078,plain,(
    ! [A_4843,B_4844] :
      ( r2_hidden('#skF_2'(A_4843,B_4844),A_4843)
      | r1_tarski(A_4843,B_4844) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_161092,plain,(
    ! [A_4843,B_4844] :
      ( ~ v1_xboole_0(A_4843)
      | r1_tarski(A_4843,B_4844) ) ),
    inference(resolution,[status(thm)],[c_161078,c_2])).

tff(c_157551,plain,(
    ! [A_14] : k2_zfmisc_1(A_14,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_157538,c_157538,c_22])).

tff(c_160949,plain,(
    ! [A_4832,B_4833,C_4834,D_4835] :
      ( k5_relset_1(A_4832,B_4833,C_4834,D_4835) = k7_relat_1(C_4834,D_4835)
      | ~ m1_subset_1(C_4834,k1_zfmisc_1(k2_zfmisc_1(A_4832,B_4833))) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_160955,plain,(
    ! [A_4832,B_4833,D_4835] : k5_relset_1(A_4832,B_4833,'#skF_5',D_4835) = k7_relat_1('#skF_5',D_4835) ),
    inference(resolution,[status(thm)],[c_157552,c_160949])).

tff(c_160965,plain,(
    ! [A_4832,B_4833,D_4835] : k5_relset_1(A_4832,B_4833,'#skF_5',D_4835) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_157689,c_160955])).

tff(c_157776,plain,(
    ! [A_4550,B_4551] :
      ( r2_hidden('#skF_2'(A_4550,B_4551),A_4550)
      | r1_tarski(A_4550,B_4551) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_157790,plain,(
    ! [A_4550,B_4551] :
      ( ~ v1_xboole_0(A_4550)
      | r1_tarski(A_4550,B_4551) ) ),
    inference(resolution,[status(thm)],[c_157776,c_2])).

tff(c_157539,plain,(
    ! [A_12] :
      ( A_12 = '#skF_5'
      | ~ v1_xboole_0(A_12) ) ),
    inference(resolution,[status(thm)],[c_157528,c_18])).

tff(c_157668,plain,(
    k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_157529,c_157539])).

tff(c_157854,plain,(
    ! [B_4557,A_4558] :
      ( B_4557 = '#skF_5'
      | A_4558 = '#skF_5'
      | k2_zfmisc_1(A_4558,B_4557) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157538,c_157538,c_157538,c_20])).

tff(c_157864,plain,
    ( u1_struct_0('#skF_4') = '#skF_5'
    | u1_struct_0('#skF_3') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_157668,c_157854])).

tff(c_157869,plain,(
    u1_struct_0('#skF_3') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_157864])).

tff(c_157599,plain,
    ( u1_struct_0('#skF_3') = '#skF_6'
    | ~ r1_tarski(u1_struct_0('#skF_3'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_163,c_157588])).

tff(c_157736,plain,(
    ~ r1_tarski(u1_struct_0('#skF_3'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_157599])).

tff(c_157870,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_157869,c_157736])).

tff(c_157879,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_157548,c_157870])).

tff(c_157880,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_157864])).

tff(c_157542,plain,(
    ~ m1_subset_1(k5_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_3','#skF_6')),u1_struct_0('#skF_4')))) ),
    inference(splitLeft,[status(thm)],[c_1653])).

tff(c_157979,plain,(
    ~ m1_subset_1(k5_relset_1(u1_struct_0('#skF_3'),'#skF_5','#skF_5','#skF_6'),k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157551,c_157880,c_157880,c_157542])).

tff(c_157983,plain,(
    ~ r1_tarski(k5_relset_1(u1_struct_0('#skF_3'),'#skF_5','#skF_5','#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_157979])).

tff(c_158057,plain,(
    ~ v1_xboole_0(k5_relset_1(u1_struct_0('#skF_3'),'#skF_5','#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_157790,c_157983])).

tff(c_160967,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_160965,c_158057])).

tff(c_160973,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_157528,c_160967])).

tff(c_160974,plain,(
    u1_struct_0('#skF_3') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_157599])).

tff(c_160978,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_160974,c_212])).

tff(c_160976,plain,(
    k2_zfmisc_1('#skF_6',u1_struct_0('#skF_4')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_160974,c_157668])).

tff(c_161005,plain,(
    ! [B_4836,A_4837] :
      ( B_4836 = '#skF_5'
      | A_4837 = '#skF_5'
      | k2_zfmisc_1(A_4837,B_4836) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157538,c_157538,c_157538,c_20])).

tff(c_161015,plain,
    ( u1_struct_0('#skF_4') = '#skF_5'
    | '#skF_5' = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_160976,c_161005])).

tff(c_161020,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_161015])).

tff(c_161035,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_161020,c_157528])).

tff(c_161039,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_160978,c_161035])).

tff(c_161040,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_161015])).

tff(c_161212,plain,(
    ~ m1_subset_1(k5_relset_1('#skF_6','#skF_5','#skF_5','#skF_6'),k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157551,c_161040,c_161040,c_160974,c_157542])).

tff(c_161216,plain,(
    ~ r1_tarski(k5_relset_1('#skF_6','#skF_5','#skF_5','#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_161212])).

tff(c_161220,plain,(
    ~ v1_xboole_0(k5_relset_1('#skF_6','#skF_5','#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_161092,c_161216])).

tff(c_163701,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_163699,c_161220])).

tff(c_163707,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_157528,c_163701])).

tff(c_163709,plain,(
    m1_subset_1(k5_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_3','#skF_6')),u1_struct_0('#skF_4')))) ),
    inference(splitRight,[status(thm)],[c_1653])).

tff(c_164154,plain,(
    m1_subset_1(k5_relset_1(u1_struct_0('#skF_3'),'#skF_5','#skF_5','#skF_6'),k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163718,c_163972,c_163972,c_163709])).

tff(c_164163,plain,
    ( v1_xboole_0(k5_relset_1(u1_struct_0('#skF_3'),'#skF_5','#skF_5','#skF_6'))
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_164154,c_28])).

tff(c_164171,plain,(
    v1_xboole_0(k5_relset_1(u1_struct_0('#skF_3'),'#skF_5','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157528,c_164163])).

tff(c_164210,plain,(
    k5_relset_1(u1_struct_0('#skF_3'),'#skF_5','#skF_5','#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_164171,c_157539])).

tff(c_163708,plain,(
    ~ v1_funct_2(k5_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_6'),u1_struct_0(k1_pre_topc('#skF_3','#skF_6')),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1653])).

tff(c_164071,plain,(
    ~ v1_funct_2(k5_relset_1(u1_struct_0('#skF_3'),'#skF_5','#skF_5','#skF_6'),u1_struct_0(k1_pre_topc('#skF_3','#skF_6')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_163972,c_163972,c_163708])).

tff(c_164217,plain,(
    ~ v1_funct_2('#skF_5',u1_struct_0(k1_pre_topc('#skF_3','#skF_6')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_164210,c_164071])).

tff(c_164237,plain,(
    u1_struct_0(k1_pre_topc('#skF_3','#skF_6')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_163716,c_164217])).

tff(c_164788,plain,(
    ! [A_5216,B_5217] :
      ( u1_struct_0(k1_pre_topc(A_5216,B_5217)) = B_5217
      | ~ m1_subset_1(B_5217,k1_zfmisc_1(u1_struct_0(A_5216)))
      | ~ l1_pre_topc(A_5216) ) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_164805,plain,
    ( u1_struct_0(k1_pre_topc('#skF_3','#skF_6')) = '#skF_6'
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_98,c_164788])).

tff(c_164812,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_164237,c_164805])).

tff(c_163911,plain,(
    ! [A_5113,A_5114,B_5115] :
      ( v1_relat_1(A_5113)
      | ~ r1_tarski(A_5113,k2_zfmisc_1(A_5114,B_5115)) ) ),
    inference(resolution,[status(thm)],[c_32,c_1678])).

tff(c_163933,plain,(
    ! [A_5114,B_5115] : v1_relat_1(k2_zfmisc_1(A_5114,B_5115)) ),
    inference(resolution,[status(thm)],[c_16,c_163911])).

tff(c_163717,plain,(
    ! [B_15] : k2_zfmisc_1('#skF_5',B_15) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_157538,c_157538,c_24])).

tff(c_164123,plain,(
    ! [C_5143,A_5144,B_5145] :
      ( v4_relat_1(C_5143,A_5144)
      | ~ m1_subset_1(C_5143,k1_zfmisc_1(k2_zfmisc_1(A_5144,B_5145))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_164249,plain,(
    ! [A_5156,A_5157,B_5158] :
      ( v4_relat_1(A_5156,A_5157)
      | ~ r1_tarski(A_5156,k2_zfmisc_1(A_5157,B_5158)) ) ),
    inference(resolution,[status(thm)],[c_32,c_164123])).

tff(c_164278,plain,(
    ! [A_5157,B_5158] : v4_relat_1(k2_zfmisc_1(A_5157,B_5158),A_5157) ),
    inference(resolution,[status(thm)],[c_16,c_164249])).

tff(c_164378,plain,(
    ! [B_5184,A_5185] :
      ( k7_relat_1(B_5184,A_5185) = B_5184
      | ~ v4_relat_1(B_5184,A_5185)
      | ~ v1_relat_1(B_5184) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_164384,plain,(
    ! [A_5157,B_5158] :
      ( k7_relat_1(k2_zfmisc_1(A_5157,B_5158),A_5157) = k2_zfmisc_1(A_5157,B_5158)
      | ~ v1_relat_1(k2_zfmisc_1(A_5157,B_5158)) ) ),
    inference(resolution,[status(thm)],[c_164278,c_164378])).

tff(c_164397,plain,(
    ! [A_5157,B_5158] : k7_relat_1(k2_zfmisc_1(A_5157,B_5158),A_5157) = k2_zfmisc_1(A_5157,B_5158) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163933,c_164384])).

tff(c_164566,plain,(
    ! [B_5201,A_5202] :
      ( k1_relat_1(k7_relat_1(B_5201,A_5202)) = A_5202
      | ~ r1_tarski(A_5202,k1_relat_1(B_5201))
      | ~ v1_relat_1(B_5201) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_164603,plain,(
    ! [B_5206] :
      ( k1_relat_1(k7_relat_1(B_5206,'#skF_5')) = '#skF_5'
      | ~ v1_relat_1(B_5206) ) ),
    inference(resolution,[status(thm)],[c_163715,c_164566])).

tff(c_164616,plain,(
    ! [B_5158] :
      ( k1_relat_1(k2_zfmisc_1('#skF_5',B_5158)) = '#skF_5'
      | ~ v1_relat_1(k2_zfmisc_1('#skF_5',B_5158)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_164397,c_164603])).

tff(c_164624,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_163933,c_163717,c_164616])).

tff(c_164813,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_164812,c_164812,c_164624])).

tff(c_163719,plain,(
    ! [A_16] : m1_subset_1('#skF_5',k1_zfmisc_1(A_16)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157538,c_26])).

tff(c_165076,plain,(
    ! [A_5229] : m1_subset_1('#skF_6',k1_zfmisc_1(A_5229)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164812,c_163719])).

tff(c_165080,plain,(
    ! [A_45,B_46] : k1_relset_1(A_45,B_46,'#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_165076,c_58])).

tff(c_165106,plain,(
    ! [A_45,B_46] : k1_relset_1(A_45,B_46,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_164813,c_165080])).

tff(c_164840,plain,(
    ! [A_16] : m1_subset_1('#skF_6',k1_zfmisc_1(A_16)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164812,c_163719])).

tff(c_164843,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_164812,c_157538])).

tff(c_114,plain,(
    ! [C_62,B_61] :
      ( v1_funct_2(C_62,k1_xboole_0,B_61)
      | k1_relset_1(k1_xboole_0,B_61,C_62) != k1_xboole_0
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_74])).

tff(c_165382,plain,(
    ! [C_5249,B_5250] :
      ( v1_funct_2(C_5249,'#skF_6',B_5250)
      | k1_relset_1('#skF_6',B_5250,C_5249) != '#skF_6'
      | ~ m1_subset_1(C_5249,k1_zfmisc_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164843,c_164843,c_164843,c_164843,c_114])).

tff(c_165385,plain,(
    ! [B_5250] :
      ( v1_funct_2('#skF_6','#skF_6',B_5250)
      | k1_relset_1('#skF_6',B_5250,'#skF_6') != '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_164840,c_165382])).

tff(c_165391,plain,(
    ! [B_5250] : v1_funct_2('#skF_6','#skF_6',B_5250) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165106,c_165385])).

tff(c_164238,plain,(
    ~ v1_funct_2('#skF_5','#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_164237,c_164217])).

tff(c_164822,plain,(
    ~ v1_funct_2('#skF_6','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_164812,c_164812,c_164812,c_164238])).

tff(c_165395,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_165391,c_164822])).

tff(c_165396,plain,(
    u1_struct_0('#skF_3') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_163861])).

tff(c_165400,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_165396,c_212])).

tff(c_165398,plain,(
    k2_zfmisc_1('#skF_6',u1_struct_0('#skF_4')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_165396,c_163754])).

tff(c_165529,plain,(
    ! [B_5265,A_5266] :
      ( B_5265 = '#skF_5'
      | A_5266 = '#skF_5'
      | k2_zfmisc_1(A_5266,B_5265) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157538,c_157538,c_157538,c_20])).

tff(c_165539,plain,
    ( u1_struct_0('#skF_4') = '#skF_5'
    | '#skF_5' = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_165398,c_165529])).

tff(c_165544,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_165539])).

tff(c_165581,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_165544,c_157528])).

tff(c_165585,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_165400,c_165581])).

tff(c_165587,plain,(
    '#skF_5' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_165539])).

tff(c_165403,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165396,c_98])).

tff(c_166213,plain,(
    ! [A_5349,B_5350] :
      ( u1_struct_0(k1_pre_topc(A_5349,B_5350)) = B_5350
      | ~ m1_subset_1(B_5350,k1_zfmisc_1(u1_struct_0(A_5349)))
      | ~ l1_pre_topc(A_5349) ) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_166222,plain,(
    ! [B_5350] :
      ( u1_struct_0(k1_pre_topc('#skF_3',B_5350)) = B_5350
      | ~ m1_subset_1(B_5350,k1_zfmisc_1('#skF_6'))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_165396,c_166213])).

tff(c_166368,plain,(
    ! [B_5358] :
      ( u1_struct_0(k1_pre_topc('#skF_3',B_5358)) = B_5358
      | ~ m1_subset_1(B_5358,k1_zfmisc_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_166222])).

tff(c_166385,plain,(
    u1_struct_0(k1_pre_topc('#skF_3','#skF_6')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_165403,c_166368])).

tff(c_165586,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_165539])).

tff(c_165662,plain,(
    m1_subset_1(k5_relset_1('#skF_6','#skF_5','#skF_5','#skF_6'),k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163718,c_165586,c_165586,c_165396,c_163709])).

tff(c_165668,plain,
    ( v1_xboole_0(k5_relset_1('#skF_6','#skF_5','#skF_5','#skF_6'))
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_165662,c_28])).

tff(c_165675,plain,(
    v1_xboole_0(k5_relset_1('#skF_6','#skF_5','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157528,c_165668])).

tff(c_165700,plain,(
    k5_relset_1('#skF_6','#skF_5','#skF_5','#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_165675,c_157539])).

tff(c_165503,plain,(
    ~ v1_funct_2(k5_relset_1('#skF_6',u1_struct_0('#skF_4'),'#skF_5','#skF_6'),u1_struct_0(k1_pre_topc('#skF_3','#skF_6')),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165396,c_163708])).

tff(c_165588,plain,(
    ~ v1_funct_2(k5_relset_1('#skF_6','#skF_5','#skF_5','#skF_6'),u1_struct_0(k1_pre_topc('#skF_3','#skF_6')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_165586,c_165586,c_165503])).

tff(c_165747,plain,(
    ~ v1_funct_2('#skF_5',u1_struct_0(k1_pre_topc('#skF_3','#skF_6')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_165700,c_165588])).

tff(c_165751,plain,(
    u1_struct_0(k1_pre_topc('#skF_3','#skF_6')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_163716,c_165747])).

tff(c_166388,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_166385,c_165751])).

tff(c_166390,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_165587,c_166388])).

tff(c_166391,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_209])).

tff(c_166401,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_166391,c_180])).

tff(c_166410,plain,(
    ! [B_15] : k2_zfmisc_1('#skF_6',B_15) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_166401,c_166401,c_24])).

tff(c_166392,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_209])).

tff(c_168965,plain,(
    ! [A_5597] :
      ( A_5597 = '#skF_6'
      | ~ v1_xboole_0(A_5597) ) ),
    inference(resolution,[status(thm)],[c_166391,c_18])).

tff(c_168972,plain,(
    u1_struct_0('#skF_3') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_166392,c_168965])).

tff(c_168978,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_6',u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_168972,c_174])).

tff(c_169049,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_166410,c_168978])).

tff(c_169100,plain,(
    ! [A_5610,B_5611] :
      ( v1_xboole_0(A_5610)
      | ~ v1_xboole_0(B_5611)
      | ~ r1_tarski(A_5610,B_5611) ) ),
    inference(resolution,[status(thm)],[c_32,c_194])).

tff(c_169103,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_169049,c_169100])).

tff(c_169115,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_166391,c_169103])).

tff(c_166402,plain,(
    ! [A_12] :
      ( A_12 = '#skF_6'
      | ~ v1_xboole_0(A_12) ) ),
    inference(resolution,[status(thm)],[c_166391,c_18])).

tff(c_169145,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_169115,c_166402])).

tff(c_168980,plain,(
    v1_funct_2('#skF_5','#skF_6',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_168972,c_102])).

tff(c_169154,plain,(
    v1_funct_2('#skF_6','#skF_6',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169145,c_168980])).

tff(c_166412,plain,(
    ! [A_16] : m1_subset_1('#skF_6',k1_zfmisc_1(A_16)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_166401,c_26])).

tff(c_173045,plain,(
    ! [A_5977,B_5978] :
      ( u1_struct_0(k1_pre_topc(A_5977,B_5978)) = B_5978
      | ~ m1_subset_1(B_5978,k1_zfmisc_1(u1_struct_0(A_5977)))
      | ~ l1_pre_topc(A_5977) ) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_173057,plain,(
    ! [A_5977] :
      ( u1_struct_0(k1_pre_topc(A_5977,'#skF_6')) = '#skF_6'
      | ~ l1_pre_topc(A_5977) ) ),
    inference(resolution,[status(thm)],[c_166412,c_173045])).

tff(c_173061,plain,(
    ! [A_5979] :
      ( u1_struct_0(k1_pre_topc(A_5979,'#skF_6')) = '#skF_6'
      | ~ l1_pre_topc(A_5979) ) ),
    inference(resolution,[status(thm)],[c_166412,c_173045])).

tff(c_169018,plain,(
    ! [C_5600,A_5601,B_5602] :
      ( v1_relat_1(C_5600)
      | ~ m1_subset_1(C_5600,k1_zfmisc_1(k2_zfmisc_1(A_5601,B_5602))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_169029,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_166412,c_169018])).

tff(c_166408,plain,(
    ! [A_16] : r1_tarski('#skF_6',A_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_166401,c_164])).

tff(c_169240,plain,(
    ! [B_5626,A_5627] :
      ( B_5626 = A_5627
      | ~ r1_tarski(B_5626,A_5627)
      | ~ r1_tarski(A_5627,B_5626) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_169256,plain,(
    ! [A_5628] :
      ( A_5628 = '#skF_6'
      | ~ r1_tarski(A_5628,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_166408,c_169240])).

tff(c_169268,plain,(
    ! [A_30] :
      ( k7_relat_1('#skF_6',A_30) = '#skF_6'
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_40,c_169256])).

tff(c_169278,plain,(
    ! [A_30] : k7_relat_1('#skF_6',A_30) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_169029,c_169268])).

tff(c_172379,plain,(
    ! [A_5893,B_5894,C_5895,D_5896] :
      ( k5_relset_1(A_5893,B_5894,C_5895,D_5896) = k7_relat_1(C_5895,D_5896)
      | ~ m1_subset_1(C_5895,k1_zfmisc_1(k2_zfmisc_1(A_5893,B_5894))) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_172392,plain,(
    ! [A_5893,B_5894,D_5896] : k5_relset_1(A_5893,B_5894,'#skF_6',D_5896) = k7_relat_1('#skF_6',D_5896) ),
    inference(resolution,[status(thm)],[c_166412,c_172379])).

tff(c_172399,plain,(
    ! [A_5893,B_5894,D_5896] : k5_relset_1(A_5893,B_5894,'#skF_6',D_5896) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_169278,c_172392])).

tff(c_169977,plain,(
    ! [A_5715,B_5716] :
      ( u1_struct_0(k1_pre_topc(A_5715,B_5716)) = B_5716
      | ~ m1_subset_1(B_5716,k1_zfmisc_1(u1_struct_0(A_5715)))
      | ~ l1_pre_topc(A_5715) ) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_169988,plain,(
    ! [B_5716] :
      ( u1_struct_0(k1_pre_topc('#skF_3',B_5716)) = B_5716
      | ~ m1_subset_1(B_5716,k1_zfmisc_1('#skF_6'))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_168972,c_169977])).

tff(c_170045,plain,(
    ! [B_5720] :
      ( u1_struct_0(k1_pre_topc('#skF_3',B_5720)) = B_5720
      | ~ m1_subset_1(B_5720,k1_zfmisc_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_169988])).

tff(c_170059,plain,(
    u1_struct_0(k1_pre_topc('#skF_3','#skF_6')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_166412,c_170045])).

tff(c_166403,plain,(
    v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_166391,c_44])).

tff(c_166501,plain,(
    ! [A_5368] : m1_subset_1('#skF_6',k1_zfmisc_1(A_5368)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_166401,c_26])).

tff(c_52,plain,(
    ! [C_41,A_39,B_40] :
      ( v1_relat_1(C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_166512,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_166501,c_52])).

tff(c_166687,plain,(
    ! [B_5387,A_5388] :
      ( B_5387 = A_5388
      | ~ r1_tarski(B_5387,A_5388)
      | ~ r1_tarski(A_5388,B_5387) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_166703,plain,(
    ! [A_5389] :
      ( A_5389 = '#skF_6'
      | ~ r1_tarski(A_5389,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_166408,c_166687])).

tff(c_166715,plain,(
    ! [A_30] :
      ( k7_relat_1('#skF_6',A_30) = '#skF_6'
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_40,c_166703])).

tff(c_166725,plain,(
    ! [A_30] : k7_relat_1('#skF_6',A_30) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_166512,c_166715])).

tff(c_168931,plain,(
    ! [A_5592,B_5593,C_5594,D_5595] :
      ( k5_relset_1(A_5592,B_5593,C_5594,D_5595) = k7_relat_1(C_5594,D_5595)
      | ~ m1_subset_1(C_5594,k1_zfmisc_1(k2_zfmisc_1(A_5592,B_5593))) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_168937,plain,(
    ! [A_5592,B_5593,D_5595] : k5_relset_1(A_5592,B_5593,'#skF_6',D_5595) = k7_relat_1('#skF_6',D_5595) ),
    inference(resolution,[status(thm)],[c_166412,c_168931])).

tff(c_168947,plain,(
    ! [A_5592,B_5593,D_5595] : k5_relset_1(A_5592,B_5593,'#skF_6',D_5595) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_166725,c_168937])).

tff(c_166435,plain,(
    ! [A_5362] :
      ( A_5362 = '#skF_6'
      | ~ v1_xboole_0(A_5362) ) ),
    inference(resolution,[status(thm)],[c_166391,c_18])).

tff(c_166442,plain,(
    u1_struct_0('#skF_3') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_166392,c_166435])).

tff(c_166448,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_6',u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_166442,c_100])).

tff(c_166582,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_166410,c_166448])).

tff(c_166588,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_166582,c_28])).

tff(c_166596,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_166391,c_166588])).

tff(c_166607,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_166596,c_166402])).

tff(c_166426,plain,(
    ~ v1_funct_1(k5_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_166661,plain,(
    ~ v1_funct_1(k5_relset_1('#skF_6',u1_struct_0('#skF_4'),'#skF_6','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_166607,c_166442,c_166426])).

tff(c_168951,plain,(
    ~ v1_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_168947,c_166661])).

tff(c_168954,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_166403,c_168951])).

tff(c_168955,plain,
    ( ~ v1_funct_2(k5_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_6'),u1_struct_0(k1_pre_topc('#skF_3','#skF_6')),u1_struct_0('#skF_4'))
    | ~ m1_subset_1(k5_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_3','#skF_6')),u1_struct_0('#skF_4')))) ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_169323,plain,
    ( ~ v1_funct_2(k5_relset_1('#skF_6',u1_struct_0('#skF_4'),'#skF_6','#skF_6'),u1_struct_0(k1_pre_topc('#skF_3','#skF_6')),u1_struct_0('#skF_4'))
    | ~ m1_subset_1(k5_relset_1('#skF_6',u1_struct_0('#skF_4'),'#skF_6','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_3','#skF_6')),u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169145,c_168972,c_169145,c_168972,c_168955])).

tff(c_169324,plain,(
    ~ m1_subset_1(k5_relset_1('#skF_6',u1_struct_0('#skF_4'),'#skF_6','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_3','#skF_6')),u1_struct_0('#skF_4')))) ),
    inference(splitLeft,[status(thm)],[c_169323])).

tff(c_170087,plain,(
    ~ m1_subset_1(k5_relset_1('#skF_6',u1_struct_0('#skF_4'),'#skF_6','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_6',u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_170059,c_169324])).

tff(c_170089,plain,(
    ~ m1_subset_1(k5_relset_1('#skF_6',u1_struct_0('#skF_4'),'#skF_6','#skF_6'),k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_166410,c_170087])).

tff(c_172401,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172399,c_170089])).

tff(c_172407,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_166412,c_172401])).

tff(c_172409,plain,(
    m1_subset_1(k5_relset_1('#skF_6',u1_struct_0('#skF_4'),'#skF_6','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_3','#skF_6')),u1_struct_0('#skF_4')))) ),
    inference(splitRight,[status(thm)],[c_169323])).

tff(c_172526,plain,(
    r1_tarski(k5_relset_1('#skF_6',u1_struct_0('#skF_4'),'#skF_6','#skF_6'),k2_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_3','#skF_6')),u1_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_172409,c_30])).

tff(c_173070,plain,
    ( r1_tarski(k5_relset_1('#skF_6',u1_struct_0('#skF_4'),'#skF_6','#skF_6'),k2_zfmisc_1('#skF_6',u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_173061,c_172526])).

tff(c_173085,plain,(
    r1_tarski(k5_relset_1('#skF_6',u1_struct_0('#skF_4'),'#skF_6','#skF_6'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_166410,c_173070])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_172490,plain,(
    ! [C_5912,B_5913,A_5914] :
      ( r2_hidden(C_5912,B_5913)
      | ~ r2_hidden(C_5912,A_5914)
      | ~ r1_tarski(A_5914,B_5913) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_172789,plain,(
    ! [A_5961,B_5962] :
      ( r2_hidden('#skF_1'(A_5961),B_5962)
      | ~ r1_tarski(A_5961,B_5962)
      | v1_xboole_0(A_5961) ) ),
    inference(resolution,[status(thm)],[c_4,c_172490])).

tff(c_172999,plain,(
    ! [B_5974,A_5975] :
      ( ~ r1_tarski(B_5974,'#skF_1'(A_5975))
      | ~ r1_tarski(A_5975,B_5974)
      | v1_xboole_0(A_5975) ) ),
    inference(resolution,[status(thm)],[c_172789,c_50])).

tff(c_173017,plain,(
    ! [A_5975] :
      ( ~ r1_tarski(A_5975,'#skF_6')
      | v1_xboole_0(A_5975) ) ),
    inference(resolution,[status(thm)],[c_166408,c_172999])).

tff(c_173110,plain,(
    v1_xboole_0(k5_relset_1('#skF_6',u1_struct_0('#skF_4'),'#skF_6','#skF_6')) ),
    inference(resolution,[status(thm)],[c_173085,c_173017])).

tff(c_173146,plain,(
    k5_relset_1('#skF_6',u1_struct_0('#skF_4'),'#skF_6','#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_173110,c_166402])).

tff(c_172408,plain,(
    ~ v1_funct_2(k5_relset_1('#skF_6',u1_struct_0('#skF_4'),'#skF_6','#skF_6'),u1_struct_0(k1_pre_topc('#skF_3','#skF_6')),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_169323])).

tff(c_173157,plain,(
    ~ v1_funct_2('#skF_6',u1_struct_0(k1_pre_topc('#skF_3','#skF_6')),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173146,c_172408])).

tff(c_173186,plain,
    ( ~ v1_funct_2('#skF_6','#skF_6',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_173057,c_173157])).

tff(c_173189,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_169154,c_173186])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:09:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 37.04/25.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 37.31/25.64  
% 37.31/25.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 37.31/25.64  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_pre_topc > k5_relset_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 37.31/25.64  
% 37.31/25.64  %Foreground sorts:
% 37.31/25.64  
% 37.31/25.64  
% 37.31/25.64  %Background operators:
% 37.31/25.64  
% 37.31/25.64  
% 37.31/25.64  %Foreground operators:
% 37.31/25.64  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 37.31/25.64  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 37.31/25.64  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 37.31/25.64  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 37.31/25.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 37.31/25.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 37.31/25.64  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 37.31/25.64  tff('#skF_1', type, '#skF_1': $i > $i).
% 37.31/25.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 37.31/25.64  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 37.31/25.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 37.31/25.64  tff('#skF_5', type, '#skF_5': $i).
% 37.31/25.64  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 37.31/25.64  tff('#skF_6', type, '#skF_6': $i).
% 37.31/25.64  tff('#skF_3', type, '#skF_3': $i).
% 37.31/25.64  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 37.31/25.64  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 37.31/25.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 37.31/25.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 37.31/25.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 37.31/25.64  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 37.31/25.64  tff('#skF_4', type, '#skF_4': $i).
% 37.31/25.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 37.31/25.64  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 37.31/25.64  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 37.31/25.64  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 37.31/25.64  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 37.31/25.64  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 37.31/25.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 37.31/25.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 37.31/25.64  
% 37.69/25.70  tff(f_234, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: ((~v2_struct_0(B) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ((v1_funct_1(k5_relset_1(u1_struct_0(A), u1_struct_0(B), C, D)) & v1_funct_2(k5_relset_1(u1_struct_0(A), u1_struct_0(B), C, D), u1_struct_0(k1_pre_topc(A, D)), u1_struct_0(B))) & m1_subset_1(k5_relset_1(u1_struct_0(A), u1_struct_0(B), C, D), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(A, D)), u1_struct_0(B))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_pre_topc)).
% 37.69/25.70  tff(f_60, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 37.69/25.70  tff(f_71, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 37.69/25.70  tff(f_58, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 37.69/25.70  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 37.69/25.70  tff(f_116, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 37.69/25.70  tff(f_120, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 37.69/25.70  tff(f_130, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 37.69/25.70  tff(f_176, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 37.69/25.70  tff(f_99, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 37.69/25.70  tff(f_134, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 37.69/25.70  tff(f_138, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => m1_subset_1(k5_relset_1(A, C, D, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_relset_1)).
% 37.69/25.70  tff(f_103, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_1)).
% 37.69/25.70  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 37.69/25.70  tff(f_126, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 37.69/25.70  tff(f_89, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 37.69/25.70  tff(f_202, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((k1_relset_1(A, B, C) = A) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_funct_2)).
% 37.69/25.70  tff(f_158, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => ((v1_funct_1(C) & ~v1_xboole_0(C)) & v1_funct_2(C, A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc6_funct_2)).
% 37.69/25.70  tff(f_67, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 37.69/25.70  tff(f_209, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (u1_struct_0(k1_pre_topc(A, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_pre_topc)).
% 37.69/25.70  tff(f_111, axiom, (![A, B]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k7_relat_1(A, B)) & v1_funct_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_funct_1)).
% 37.69/25.70  tff(f_52, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 37.69/25.70  tff(f_93, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 37.69/25.70  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 37.69/25.70  tff(c_110, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_234])).
% 37.69/25.70  tff(c_26, plain, (![A_16]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 37.69/25.70  tff(c_156, plain, (![A_102, B_103]: (r1_tarski(A_102, B_103) | ~m1_subset_1(A_102, k1_zfmisc_1(B_103)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 37.69/25.70  tff(c_164, plain, (![A_16]: (r1_tarski(k1_xboole_0, A_16))), inference(resolution, [status(thm)], [c_26, c_156])).
% 37.69/25.70  tff(c_22, plain, (![A_14]: (k2_zfmisc_1(A_14, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 37.69/25.70  tff(c_165, plain, (![A_104]: (r1_tarski(k1_xboole_0, A_104))), inference(resolution, [status(thm)], [c_26, c_156])).
% 37.69/25.70  tff(c_146, plain, (![A_100]: (v1_xboole_0(A_100) | r2_hidden('#skF_1'(A_100), A_100))), inference(cnfTransformation, [status(thm)], [f_31])).
% 37.69/25.70  tff(c_50, plain, (![B_38, A_37]: (~r1_tarski(B_38, A_37) | ~r2_hidden(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_116])).
% 37.69/25.70  tff(c_153, plain, (![A_100]: (~r1_tarski(A_100, '#skF_1'(A_100)) | v1_xboole_0(A_100))), inference(resolution, [status(thm)], [c_146, c_50])).
% 37.69/25.70  tff(c_170, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_165, c_153])).
% 37.69/25.70  tff(c_100, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_234])).
% 37.69/25.70  tff(c_1678, plain, (![C_280, A_281, B_282]: (v1_relat_1(C_280) | ~m1_subset_1(C_280, k1_zfmisc_1(k2_zfmisc_1(A_281, B_282))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 37.69/25.70  tff(c_1695, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_100, c_1678])).
% 37.69/25.70  tff(c_102, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_234])).
% 37.69/25.70  tff(c_26416, plain, (![A_1210, B_1211, C_1212]: (k1_relset_1(A_1210, B_1211, C_1212)=k1_relat_1(C_1212) | ~m1_subset_1(C_1212, k1_zfmisc_1(k2_zfmisc_1(A_1210, B_1211))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 37.69/25.70  tff(c_26444, plain, (k1_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_100, c_26416])).
% 37.69/25.70  tff(c_27984, plain, (![B_1312, A_1313, C_1314]: (k1_xboole_0=B_1312 | k1_relset_1(A_1313, B_1312, C_1314)=A_1313 | ~v1_funct_2(C_1314, A_1313, B_1312) | ~m1_subset_1(C_1314, k1_zfmisc_1(k2_zfmisc_1(A_1313, B_1312))))), inference(cnfTransformation, [status(thm)], [f_176])).
% 37.69/25.70  tff(c_28001, plain, (u1_struct_0('#skF_4')=k1_xboole_0 | k1_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5')=u1_struct_0('#skF_3') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_100, c_27984])).
% 37.69/25.70  tff(c_28018, plain, (u1_struct_0('#skF_4')=k1_xboole_0 | u1_struct_0('#skF_3')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_26444, c_28001])).
% 37.69/25.70  tff(c_28025, plain, (u1_struct_0('#skF_3')=k1_relat_1('#skF_5')), inference(splitLeft, [status(thm)], [c_28018])).
% 37.69/25.70  tff(c_98, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_234])).
% 37.69/25.70  tff(c_163, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_98, c_156])).
% 37.69/25.70  tff(c_28038, plain, (r1_tarski('#skF_6', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_28025, c_163])).
% 37.69/25.70  tff(c_42, plain, (![B_33, A_32]: (k1_relat_1(k7_relat_1(B_33, A_32))=A_32 | ~r1_tarski(A_32, k1_relat_1(B_33)) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_99])).
% 37.69/25.70  tff(c_28071, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_6'))='#skF_6' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_28038, c_42])).
% 37.69/25.70  tff(c_28083, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_6'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1695, c_28071])).
% 37.69/25.70  tff(c_27079, plain, (![A_1258, B_1259, C_1260, D_1261]: (k5_relset_1(A_1258, B_1259, C_1260, D_1261)=k7_relat_1(C_1260, D_1261) | ~m1_subset_1(C_1260, k1_zfmisc_1(k2_zfmisc_1(A_1258, B_1259))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 37.69/25.70  tff(c_27100, plain, (![D_1261]: (k5_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', D_1261)=k7_relat_1('#skF_5', D_1261))), inference(resolution, [status(thm)], [c_100, c_27079])).
% 37.69/25.70  tff(c_27693, plain, (![A_1304, C_1305, D_1306, B_1307]: (m1_subset_1(k5_relset_1(A_1304, C_1305, D_1306, B_1307), k1_zfmisc_1(k2_zfmisc_1(B_1307, C_1305))) | ~m1_subset_1(D_1306, k1_zfmisc_1(k2_zfmisc_1(A_1304, C_1305))))), inference(cnfTransformation, [status(thm)], [f_138])).
% 37.69/25.70  tff(c_27722, plain, (![D_1261]: (m1_subset_1(k7_relat_1('#skF_5', D_1261), k1_zfmisc_1(k2_zfmisc_1(D_1261, u1_struct_0('#skF_4')))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))))), inference(superposition, [status(thm), theory('equality')], [c_27100, c_27693])).
% 37.69/25.70  tff(c_27748, plain, (![D_1308]: (m1_subset_1(k7_relat_1('#skF_5', D_1308), k1_zfmisc_1(k2_zfmisc_1(D_1308, u1_struct_0('#skF_4')))))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_27722])).
% 37.69/25.70  tff(c_58, plain, (![A_45, B_46, C_47]: (k1_relset_1(A_45, B_46, C_47)=k1_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 37.69/25.70  tff(c_27789, plain, (![D_1308]: (k1_relset_1(D_1308, u1_struct_0('#skF_4'), k7_relat_1('#skF_5', D_1308))=k1_relat_1(k7_relat_1('#skF_5', D_1308)))), inference(resolution, [status(thm)], [c_27748, c_58])).
% 37.69/25.70  tff(c_27743, plain, (![D_1261]: (m1_subset_1(k7_relat_1('#skF_5', D_1261), k1_zfmisc_1(k2_zfmisc_1(D_1261, u1_struct_0('#skF_4')))))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_27722])).
% 37.69/25.70  tff(c_28012, plain, (![D_1261]: (u1_struct_0('#skF_4')=k1_xboole_0 | k1_relset_1(D_1261, u1_struct_0('#skF_4'), k7_relat_1('#skF_5', D_1261))=D_1261 | ~v1_funct_2(k7_relat_1('#skF_5', D_1261), D_1261, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_27743, c_27984])).
% 37.69/25.70  tff(c_33847, plain, (![D_1261]: (u1_struct_0('#skF_4')=k1_xboole_0 | k1_relat_1(k7_relat_1('#skF_5', D_1261))=D_1261 | ~v1_funct_2(k7_relat_1('#skF_5', D_1261), D_1261, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_27789, c_28012])).
% 37.69/25.70  tff(c_33848, plain, (u1_struct_0('#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_33847])).
% 37.69/25.70  tff(c_44, plain, (![A_34]: (v1_funct_1(A_34) | ~v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_103])).
% 37.69/25.70  tff(c_181, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_170, c_44])).
% 37.69/25.70  tff(c_16, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 37.69/25.70  tff(c_32, plain, (![A_20, B_21]: (m1_subset_1(A_20, k1_zfmisc_1(B_21)) | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_71])).
% 37.69/25.70  tff(c_1731, plain, (![A_286, A_287, B_288]: (v1_relat_1(A_286) | ~r1_tarski(A_286, k2_zfmisc_1(A_287, B_288)))), inference(resolution, [status(thm)], [c_32, c_1678])).
% 37.69/25.70  tff(c_1756, plain, (![A_287, B_288]: (v1_relat_1(k2_zfmisc_1(A_287, B_288)))), inference(resolution, [status(thm)], [c_16, c_1731])).
% 37.69/25.70  tff(c_24, plain, (![B_15]: (k2_zfmisc_1(k1_xboole_0, B_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 37.69/25.70  tff(c_3380, plain, (![C_468, A_469, B_470]: (v4_relat_1(C_468, A_469) | ~m1_subset_1(C_468, k1_zfmisc_1(k2_zfmisc_1(A_469, B_470))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 37.69/25.70  tff(c_3593, plain, (![A_504, A_505, B_506]: (v4_relat_1(A_504, A_505) | ~r1_tarski(A_504, k2_zfmisc_1(A_505, B_506)))), inference(resolution, [status(thm)], [c_32, c_3380])).
% 37.69/25.70  tff(c_3627, plain, (![A_505, B_506]: (v4_relat_1(k2_zfmisc_1(A_505, B_506), A_505))), inference(resolution, [status(thm)], [c_16, c_3593])).
% 37.69/25.70  tff(c_3647, plain, (![B_514, A_515]: (k7_relat_1(B_514, A_515)=B_514 | ~v4_relat_1(B_514, A_515) | ~v1_relat_1(B_514))), inference(cnfTransformation, [status(thm)], [f_89])).
% 37.69/25.70  tff(c_3653, plain, (![A_505, B_506]: (k7_relat_1(k2_zfmisc_1(A_505, B_506), A_505)=k2_zfmisc_1(A_505, B_506) | ~v1_relat_1(k2_zfmisc_1(A_505, B_506)))), inference(resolution, [status(thm)], [c_3627, c_3647])).
% 37.69/25.70  tff(c_3669, plain, (![A_505, B_506]: (k7_relat_1(k2_zfmisc_1(A_505, B_506), A_505)=k2_zfmisc_1(A_505, B_506))), inference(demodulation, [status(thm), theory('equality')], [c_1756, c_3653])).
% 37.69/25.70  tff(c_3991, plain, (![B_546, A_547]: (k1_relat_1(k7_relat_1(B_546, A_547))=A_547 | ~r1_tarski(A_547, k1_relat_1(B_546)) | ~v1_relat_1(B_546))), inference(cnfTransformation, [status(thm)], [f_99])).
% 37.69/25.70  tff(c_4012, plain, (![B_548]: (k1_relat_1(k7_relat_1(B_548, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_548))), inference(resolution, [status(thm)], [c_164, c_3991])).
% 37.69/25.70  tff(c_4025, plain, (![B_506]: (k1_relat_1(k2_zfmisc_1(k1_xboole_0, B_506))=k1_xboole_0 | ~v1_relat_1(k2_zfmisc_1(k1_xboole_0, B_506)))), inference(superposition, [status(thm), theory('equality')], [c_3669, c_4012])).
% 37.69/25.70  tff(c_4033, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1756, c_24, c_4025])).
% 37.69/25.70  tff(c_26440, plain, (![A_1210, B_1211]: (k1_relset_1(A_1210, B_1211, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_26416])).
% 37.69/25.70  tff(c_26446, plain, (![A_1210, B_1211]: (k1_relset_1(A_1210, B_1211, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4033, c_26440])).
% 37.69/25.70  tff(c_28281, plain, (![C_1319, A_1320, B_1321]: (v1_funct_2(C_1319, A_1320, B_1321) | k1_relset_1(A_1320, B_1321, C_1319)!=A_1320 | ~m1_subset_1(C_1319, k1_zfmisc_1(k2_zfmisc_1(A_1320, B_1321))) | ~v1_funct_1(C_1319))), inference(cnfTransformation, [status(thm)], [f_202])).
% 37.69/25.70  tff(c_28305, plain, (![A_1320, B_1321]: (v1_funct_2(k1_xboole_0, A_1320, B_1321) | k1_relset_1(A_1320, B_1321, k1_xboole_0)!=A_1320 | ~v1_funct_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_28281])).
% 37.69/25.70  tff(c_28314, plain, (![A_1320, B_1321]: (v1_funct_2(k1_xboole_0, A_1320, B_1321) | k1_xboole_0!=A_1320)), inference(demodulation, [status(thm), theory('equality')], [c_181, c_26446, c_28305])).
% 37.69/25.70  tff(c_28469, plain, (![C_1326, A_1327, B_1328]: (~v1_xboole_0(C_1326) | ~v1_funct_2(C_1326, A_1327, B_1328) | ~v1_funct_1(C_1326) | ~m1_subset_1(C_1326, k1_zfmisc_1(k2_zfmisc_1(A_1327, B_1328))) | v1_xboole_0(B_1328) | v1_xboole_0(A_1327))), inference(cnfTransformation, [status(thm)], [f_158])).
% 37.69/25.70  tff(c_28496, plain, (![A_1327, B_1328]: (~v1_xboole_0(k1_xboole_0) | ~v1_funct_2(k1_xboole_0, A_1327, B_1328) | ~v1_funct_1(k1_xboole_0) | v1_xboole_0(B_1328) | v1_xboole_0(A_1327))), inference(resolution, [status(thm)], [c_26, c_28469])).
% 37.69/25.70  tff(c_28519, plain, (![A_1330, B_1331]: (~v1_funct_2(k1_xboole_0, A_1330, B_1331) | v1_xboole_0(B_1331) | v1_xboole_0(A_1330))), inference(demodulation, [status(thm), theory('equality')], [c_181, c_170, c_28496])).
% 37.69/25.70  tff(c_28526, plain, (![B_1321, A_1320]: (v1_xboole_0(B_1321) | v1_xboole_0(A_1320) | k1_xboole_0!=A_1320)), inference(resolution, [status(thm)], [c_28314, c_28519])).
% 37.69/25.70  tff(c_28532, plain, (![A_1332]: (v1_xboole_0(A_1332) | k1_xboole_0!=A_1332)), inference(splitLeft, [status(thm)], [c_28526])).
% 37.69/25.70  tff(c_194, plain, (![B_110, A_111]: (v1_xboole_0(B_110) | ~m1_subset_1(B_110, k1_zfmisc_1(A_111)) | ~v1_xboole_0(A_111))), inference(cnfTransformation, [status(thm)], [f_67])).
% 37.69/25.70  tff(c_208, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_100, c_194])).
% 37.69/25.70  tff(c_1709, plain, (~v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_208])).
% 37.69/25.70  tff(c_28035, plain, (~v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_5'), u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_28025, c_1709])).
% 37.69/25.70  tff(c_28577, plain, (k2_zfmisc_1(k1_relat_1('#skF_5'), u1_struct_0('#skF_4'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_28532, c_28035])).
% 37.69/25.70  tff(c_33868, plain, (k2_zfmisc_1(k1_relat_1('#skF_5'), k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_33848, c_28577])).
% 37.69/25.70  tff(c_33903, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_33868])).
% 37.69/25.70  tff(c_33905, plain, (u1_struct_0('#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_33847])).
% 37.69/25.70  tff(c_28092, plain, (![B_1315, C_1316, A_1317]: (k1_xboole_0=B_1315 | v1_funct_2(C_1316, A_1317, B_1315) | k1_relset_1(A_1317, B_1315, C_1316)!=A_1317 | ~m1_subset_1(C_1316, k1_zfmisc_1(k2_zfmisc_1(A_1317, B_1315))))), inference(cnfTransformation, [status(thm)], [f_176])).
% 37.69/25.70  tff(c_28117, plain, (![D_1261]: (u1_struct_0('#skF_4')=k1_xboole_0 | v1_funct_2(k7_relat_1('#skF_5', D_1261), D_1261, u1_struct_0('#skF_4')) | k1_relset_1(D_1261, u1_struct_0('#skF_4'), k7_relat_1('#skF_5', D_1261))!=D_1261)), inference(resolution, [status(thm)], [c_27743, c_28092])).
% 37.69/25.70  tff(c_34196, plain, (![D_1261]: (u1_struct_0('#skF_4')=k1_xboole_0 | v1_funct_2(k7_relat_1('#skF_5', D_1261), D_1261, u1_struct_0('#skF_4')) | k1_relat_1(k7_relat_1('#skF_5', D_1261))!=D_1261)), inference(demodulation, [status(thm), theory('equality')], [c_27789, c_28117])).
% 37.69/25.70  tff(c_34198, plain, (![D_1578]: (v1_funct_2(k7_relat_1('#skF_5', D_1578), D_1578, u1_struct_0('#skF_4')) | k1_relat_1(k7_relat_1('#skF_5', D_1578))!=D_1578)), inference(negUnitSimplification, [status(thm)], [c_33905, c_34196])).
% 37.69/25.70  tff(c_26570, plain, (![A_1227, B_1228]: (u1_struct_0(k1_pre_topc(A_1227, B_1228))=B_1228 | ~m1_subset_1(B_1228, k1_zfmisc_1(u1_struct_0(A_1227))) | ~l1_pre_topc(A_1227))), inference(cnfTransformation, [status(thm)], [f_209])).
% 37.69/25.70  tff(c_26581, plain, (u1_struct_0(k1_pre_topc('#skF_3', '#skF_6'))='#skF_6' | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_98, c_26570])).
% 37.69/25.70  tff(c_26590, plain, (u1_struct_0(k1_pre_topc('#skF_3', '#skF_6'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_110, c_26581])).
% 37.69/25.70  tff(c_3082, plain, (![A_431, B_432, C_433, D_434]: (k5_relset_1(A_431, B_432, C_433, D_434)=k7_relat_1(C_433, D_434) | ~m1_subset_1(C_433, k1_zfmisc_1(k2_zfmisc_1(A_431, B_432))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 37.69/25.70  tff(c_3100, plain, (![D_434]: (k5_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', D_434)=k7_relat_1('#skF_5', D_434))), inference(resolution, [status(thm)], [c_100, c_3082])).
% 37.69/25.70  tff(c_3228, plain, (![A_454, C_455, D_456, B_457]: (m1_subset_1(k5_relset_1(A_454, C_455, D_456, B_457), k1_zfmisc_1(k2_zfmisc_1(B_457, C_455))) | ~m1_subset_1(D_456, k1_zfmisc_1(k2_zfmisc_1(A_454, C_455))))), inference(cnfTransformation, [status(thm)], [f_138])).
% 37.69/25.70  tff(c_3257, plain, (![D_434]: (m1_subset_1(k7_relat_1('#skF_5', D_434), k1_zfmisc_1(k2_zfmisc_1(D_434, u1_struct_0('#skF_4')))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))))), inference(superposition, [status(thm), theory('equality')], [c_3100, c_3228])).
% 37.69/25.70  tff(c_3278, plain, (![D_434]: (m1_subset_1(k7_relat_1('#skF_5', D_434), k1_zfmisc_1(k2_zfmisc_1(D_434, u1_struct_0('#skF_4')))))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_3257])).
% 37.69/25.70  tff(c_2407, plain, (![A_377, B_378]: (u1_struct_0(k1_pre_topc(A_377, B_378))=B_378 | ~m1_subset_1(B_378, k1_zfmisc_1(u1_struct_0(A_377))) | ~l1_pre_topc(A_377))), inference(cnfTransformation, [status(thm)], [f_209])).
% 37.69/25.70  tff(c_2414, plain, (u1_struct_0(k1_pre_topc('#skF_3', '#skF_6'))='#skF_6' | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_98, c_2407])).
% 37.69/25.70  tff(c_2422, plain, (u1_struct_0(k1_pre_topc('#skF_3', '#skF_6'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_110, c_2414])).
% 37.69/25.70  tff(c_238, plain, (![C_118, A_119, B_120]: (v1_relat_1(C_118) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 37.69/25.70  tff(c_255, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_100, c_238])).
% 37.69/25.70  tff(c_104, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_234])).
% 37.69/25.70  tff(c_46, plain, (![A_35, B_36]: (v1_funct_1(k7_relat_1(A_35, B_36)) | ~v1_funct_1(A_35) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_111])).
% 37.69/25.70  tff(c_1587, plain, (![A_266, B_267, C_268, D_269]: (k5_relset_1(A_266, B_267, C_268, D_269)=k7_relat_1(C_268, D_269) | ~m1_subset_1(C_268, k1_zfmisc_1(k2_zfmisc_1(A_266, B_267))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 37.69/25.70  tff(c_1605, plain, (![D_269]: (k5_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', D_269)=k7_relat_1('#skF_5', D_269))), inference(resolution, [status(thm)], [c_100, c_1587])).
% 37.69/25.70  tff(c_96, plain, (~m1_subset_1(k5_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_3', '#skF_6')), u1_struct_0('#skF_4')))) | ~v1_funct_2(k5_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', '#skF_6'), u1_struct_0(k1_pre_topc('#skF_3', '#skF_6')), u1_struct_0('#skF_4')) | ~v1_funct_1(k5_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_234])).
% 37.69/25.70  tff(c_213, plain, (~v1_funct_1(k5_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_96])).
% 37.69/25.70  tff(c_1630, plain, (~v1_funct_1(k7_relat_1('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1605, c_213])).
% 37.69/25.70  tff(c_1645, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_1630])).
% 37.69/25.70  tff(c_1652, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_255, c_104, c_1645])).
% 37.69/25.70  tff(c_1653, plain, (~v1_funct_2(k5_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', '#skF_6'), u1_struct_0(k1_pre_topc('#skF_3', '#skF_6')), u1_struct_0('#skF_4')) | ~m1_subset_1(k5_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_3', '#skF_6')), u1_struct_0('#skF_4'))))), inference(splitRight, [status(thm)], [c_96])).
% 37.69/25.70  tff(c_1781, plain, (~m1_subset_1(k5_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_3', '#skF_6')), u1_struct_0('#skF_4'))))), inference(splitLeft, [status(thm)], [c_1653])).
% 37.69/25.70  tff(c_2425, plain, (~m1_subset_1(k5_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_6', u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_2422, c_1781])).
% 37.69/25.70  tff(c_3139, plain, (~m1_subset_1(k7_relat_1('#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_6', u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_3100, c_2425])).
% 37.69/25.70  tff(c_3293, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3278, c_3139])).
% 37.69/25.70  tff(c_3294, plain, (~v1_funct_2(k5_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', '#skF_6'), u1_struct_0(k1_pre_topc('#skF_3', '#skF_6')), u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_1653])).
% 37.69/25.70  tff(c_26595, plain, (~v1_funct_2(k5_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', '#skF_6'), '#skF_6', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_26590, c_3294])).
% 37.69/25.70  tff(c_27244, plain, (~v1_funct_2(k7_relat_1('#skF_5', '#skF_6'), '#skF_6', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_27100, c_26595])).
% 37.69/25.70  tff(c_34201, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_6'))!='#skF_6'), inference(resolution, [status(thm)], [c_34198, c_27244])).
% 37.69/25.70  tff(c_34228, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28083, c_34201])).
% 37.69/25.70  tff(c_34229, plain, (![B_1321]: (v1_xboole_0(B_1321))), inference(splitRight, [status(thm)], [c_28526])).
% 37.69/25.70  tff(c_209, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_98, c_194])).
% 37.69/25.70  tff(c_212, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_209])).
% 37.69/25.70  tff(c_28036, plain, (~v1_xboole_0(k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_28025, c_212])).
% 37.69/25.70  tff(c_28040, plain, (v1_funct_2('#skF_5', k1_relat_1('#skF_5'), u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_28025, c_102])).
% 37.69/25.70  tff(c_28039, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_28025, c_100])).
% 37.69/25.70  tff(c_28472, plain, (~v1_xboole_0('#skF_5') | ~v1_funct_2('#skF_5', k1_relat_1('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_5') | v1_xboole_0(u1_struct_0('#skF_4')) | v1_xboole_0(k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_28039, c_28469])).
% 37.69/25.70  tff(c_28499, plain, (~v1_xboole_0('#skF_5') | v1_xboole_0(u1_struct_0('#skF_4')) | v1_xboole_0(k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_28040, c_28472])).
% 37.69/25.70  tff(c_28500, plain, (~v1_xboole_0('#skF_5') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_28036, c_28499])).
% 37.69/25.70  tff(c_28512, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_28500])).
% 37.69/25.70  tff(c_34312, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34229, c_28512])).
% 37.69/25.70  tff(c_34314, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_28500])).
% 37.69/25.70  tff(c_18, plain, (![B_13, A_12]: (~v1_xboole_0(B_13) | B_13=A_12 | ~v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 37.69/25.70  tff(c_180, plain, (![A_12]: (k1_xboole_0=A_12 | ~v1_xboole_0(A_12))), inference(resolution, [status(thm)], [c_170, c_18])).
% 37.69/25.70  tff(c_34351, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_34314, c_180])).
% 37.69/25.70  tff(c_34407, plain, (![A_16]: (r1_tarski('#skF_5', A_16))), inference(demodulation, [status(thm), theory('equality')], [c_34351, c_164])).
% 37.69/25.70  tff(c_34388, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_34351, c_34351, c_4033])).
% 37.69/25.70  tff(c_3333, plain, (![B_465, A_466]: (B_465=A_466 | ~r1_tarski(B_465, A_466) | ~r1_tarski(A_466, B_465))), inference(cnfTransformation, [status(thm)], [f_44])).
% 37.69/25.70  tff(c_3349, plain, (u1_struct_0('#skF_3')='#skF_6' | ~r1_tarski(u1_struct_0('#skF_3'), '#skF_6')), inference(resolution, [status(thm)], [c_163, c_3333])).
% 37.69/25.70  tff(c_3426, plain, (~r1_tarski(u1_struct_0('#skF_3'), '#skF_6')), inference(splitLeft, [status(thm)], [c_3349])).
% 37.69/25.70  tff(c_28033, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_28025, c_3426])).
% 37.69/25.70  tff(c_34569, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_34388, c_28033])).
% 37.69/25.70  tff(c_34575, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34407, c_34569])).
% 37.69/25.70  tff(c_34576, plain, (u1_struct_0('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_28018])).
% 37.69/25.70  tff(c_3295, plain, (m1_subset_1(k5_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_3', '#skF_6')), u1_struct_0('#skF_4'))))), inference(splitRight, [status(thm)], [c_1653])).
% 37.69/25.70  tff(c_28, plain, (![B_19, A_17]: (v1_xboole_0(B_19) | ~m1_subset_1(B_19, k1_zfmisc_1(A_17)) | ~v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_67])).
% 37.69/25.70  tff(c_3753, plain, (v1_xboole_0(k5_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', '#skF_6')) | ~v1_xboole_0(k2_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_3', '#skF_6')), u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_3295, c_28])).
% 37.69/25.70  tff(c_27050, plain, (v1_xboole_0(k5_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', '#skF_6')) | ~v1_xboole_0(k2_zfmisc_1('#skF_6', u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_26590, c_3753])).
% 37.69/25.70  tff(c_27051, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_6', u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_27050])).
% 37.69/25.70  tff(c_34587, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_6', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_34576, c_27051])).
% 37.69/25.70  tff(c_34601, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_170, c_22, c_34587])).
% 37.69/25.70  tff(c_34603, plain, (v1_xboole_0(k2_zfmisc_1('#skF_6', u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_27050])).
% 37.69/25.70  tff(c_34636, plain, (k2_zfmisc_1('#skF_6', u1_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_34603, c_180])).
% 37.69/25.70  tff(c_20, plain, (![B_15, A_14]: (k1_xboole_0=B_15 | k1_xboole_0=A_14 | k2_zfmisc_1(A_14, B_15)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 37.69/25.70  tff(c_34724, plain, (u1_struct_0('#skF_4')=k1_xboole_0 | k1_xboole_0='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_34636, c_20])).
% 37.69/25.70  tff(c_34727, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_34724])).
% 37.69/25.70  tff(c_34774, plain, (![A_16]: (r1_tarski('#skF_6', A_16))), inference(demodulation, [status(thm), theory('equality')], [c_34727, c_164])).
% 37.69/25.70  tff(c_34777, plain, (![A_14]: (k2_zfmisc_1(A_14, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_34727, c_34727, c_22])).
% 37.69/25.70  tff(c_74, plain, (![C_62, B_61]: (v1_funct_2(C_62, k1_xboole_0, B_61) | k1_relset_1(k1_xboole_0, B_61, C_62)!=k1_xboole_0 | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_61))))), inference(cnfTransformation, [status(thm)], [f_176])).
% 37.69/25.70  tff(c_26748, plain, (![C_1239, B_1240]: (v1_funct_2(C_1239, k1_xboole_0, B_1240) | k1_relset_1(k1_xboole_0, B_1240, C_1239)!=k1_xboole_0 | ~m1_subset_1(C_1239, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_74])).
% 37.69/25.70  tff(c_26757, plain, (![B_1240]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_1240) | k1_relset_1(k1_xboole_0, B_1240, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_26748])).
% 37.69/25.70  tff(c_26762, plain, (![B_1240]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_1240))), inference(demodulation, [status(thm), theory('equality')], [c_26446, c_26757])).
% 37.69/25.70  tff(c_34739, plain, (![B_1240]: (v1_funct_2('#skF_6', '#skF_6', B_1240))), inference(demodulation, [status(thm), theory('equality')], [c_34727, c_34727, c_26762])).
% 37.69/25.70  tff(c_80, plain, (![B_61, A_60, C_62]: (k1_xboole_0=B_61 | k1_relset_1(A_60, B_61, C_62)=A_60 | ~v1_funct_2(C_62, A_60, B_61) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_176])).
% 37.69/25.70  tff(c_35293, plain, (![B_1615, A_1616, C_1617]: (B_1615='#skF_6' | k1_relset_1(A_1616, B_1615, C_1617)=A_1616 | ~v1_funct_2(C_1617, A_1616, B_1615) | ~m1_subset_1(C_1617, k1_zfmisc_1(k2_zfmisc_1(A_1616, B_1615))))), inference(demodulation, [status(thm), theory('equality')], [c_34727, c_80])).
% 37.69/25.70  tff(c_35317, plain, (u1_struct_0('#skF_4')='#skF_6' | k1_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5')=u1_struct_0('#skF_3') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_100, c_35293])).
% 37.69/25.70  tff(c_35325, plain, (u1_struct_0('#skF_4')='#skF_6' | u1_struct_0('#skF_3')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_26444, c_35317])).
% 37.69/25.70  tff(c_35327, plain, (u1_struct_0('#skF_3')=k1_relat_1('#skF_5')), inference(splitLeft, [status(thm)], [c_35325])).
% 37.69/25.70  tff(c_34639, plain, (![A_1586, B_1587, C_1588, D_1589]: (k5_relset_1(A_1586, B_1587, C_1588, D_1589)=k7_relat_1(C_1588, D_1589) | ~m1_subset_1(C_1588, k1_zfmisc_1(k2_zfmisc_1(A_1586, B_1587))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 37.69/25.70  tff(c_34660, plain, (![D_1589]: (k5_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', D_1589)=k7_relat_1('#skF_5', D_1589))), inference(resolution, [status(thm)], [c_100, c_34639])).
% 37.69/25.70  tff(c_35329, plain, (![D_1589]: (k5_relset_1(k1_relat_1('#skF_5'), u1_struct_0('#skF_4'), '#skF_5', D_1589)=k7_relat_1('#skF_5', D_1589))), inference(demodulation, [status(thm), theory('equality')], [c_35327, c_34660])).
% 37.69/25.70  tff(c_34602, plain, (v1_xboole_0(k5_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_27050])).
% 37.69/25.70  tff(c_35854, plain, (v1_xboole_0(k5_relset_1(k1_relat_1('#skF_5'), u1_struct_0('#skF_4'), '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_35327, c_34602])).
% 37.69/25.70  tff(c_36369, plain, (v1_xboole_0(k7_relat_1('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_35329, c_35854])).
% 37.69/25.70  tff(c_34771, plain, (![A_12]: (A_12='#skF_6' | ~v1_xboole_0(A_12))), inference(demodulation, [status(thm), theory('equality')], [c_34727, c_180])).
% 37.69/25.70  tff(c_36408, plain, (k7_relat_1('#skF_5', '#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_36369, c_34771])).
% 37.69/25.70  tff(c_34783, plain, (~v1_funct_2(k7_relat_1('#skF_5', '#skF_6'), '#skF_6', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_34660, c_26595])).
% 37.69/25.70  tff(c_36421, plain, (~v1_funct_2('#skF_6', '#skF_6', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_36408, c_34783])).
% 37.69/25.70  tff(c_36430, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34739, c_36421])).
% 37.69/25.70  tff(c_36431, plain, (u1_struct_0('#skF_4')='#skF_6'), inference(splitRight, [status(thm)], [c_35325])).
% 37.69/25.70  tff(c_30, plain, (![A_20, B_21]: (r1_tarski(A_20, B_21) | ~m1_subset_1(A_20, k1_zfmisc_1(B_21)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 37.69/25.70  tff(c_174, plain, (r1_tarski('#skF_5', k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_100, c_30])).
% 37.69/25.70  tff(c_3347, plain, (k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))='#skF_5' | ~r1_tarski(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')), '#skF_5')), inference(resolution, [status(thm)], [c_174, c_3333])).
% 37.69/25.70  tff(c_3489, plain, (~r1_tarski(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')), '#skF_5')), inference(splitLeft, [status(thm)], [c_3347])).
% 37.69/25.70  tff(c_36471, plain, (~r1_tarski(k2_zfmisc_1(u1_struct_0('#skF_3'), '#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_36431, c_3489])).
% 37.69/25.70  tff(c_36480, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34774, c_34777, c_36471])).
% 37.69/25.70  tff(c_36481, plain, (u1_struct_0('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_34724])).
% 37.69/25.70  tff(c_36490, plain, (~r1_tarski(k2_zfmisc_1(u1_struct_0('#skF_3'), k1_xboole_0), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_36481, c_3489])).
% 37.69/25.70  tff(c_36501, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_164, c_22, c_36490])).
% 37.69/25.70  tff(c_36502, plain, (k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))='#skF_5'), inference(splitRight, [status(thm)], [c_3347])).
% 37.69/25.70  tff(c_36505, plain, (~v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_36502, c_1709])).
% 37.69/25.70  tff(c_36518, plain, (u1_struct_0('#skF_4')=k1_xboole_0 | u1_struct_0('#skF_3')=k1_xboole_0 | k1_xboole_0!='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_36502, c_20])).
% 37.69/25.70  tff(c_37092, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_36518])).
% 37.69/25.70  tff(c_3399, plain, (v4_relat_1('#skF_5', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_100, c_3380])).
% 37.69/25.70  tff(c_36564, plain, (![B_1694, A_1695]: (k7_relat_1(B_1694, A_1695)=B_1694 | ~v4_relat_1(B_1694, A_1695) | ~v1_relat_1(B_1694))), inference(cnfTransformation, [status(thm)], [f_89])).
% 37.69/25.70  tff(c_36570, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_3399, c_36564])).
% 37.69/25.70  tff(c_36577, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1695, c_36570])).
% 37.69/25.70  tff(c_69599, plain, (![A_3032, B_3033, C_3034, D_3035]: (k5_relset_1(A_3032, B_3033, C_3034, D_3035)=k7_relat_1(C_3034, D_3035) | ~m1_subset_1(C_3034, k1_zfmisc_1(k2_zfmisc_1(A_3032, B_3033))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 37.69/25.70  tff(c_73810, plain, (![A_3342, B_3343, A_3344, D_3345]: (k5_relset_1(A_3342, B_3343, A_3344, D_3345)=k7_relat_1(A_3344, D_3345) | ~r1_tarski(A_3344, k2_zfmisc_1(A_3342, B_3343)))), inference(resolution, [status(thm)], [c_32, c_69599])).
% 37.69/25.70  tff(c_73995, plain, (![A_3355, D_3356]: (k5_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), A_3355, D_3356)=k7_relat_1(A_3355, D_3356) | ~r1_tarski(A_3355, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_36502, c_73810])).
% 37.69/25.70  tff(c_37152, plain, (![A_1767, B_1768]: (u1_struct_0(k1_pre_topc(A_1767, B_1768))=B_1768 | ~m1_subset_1(B_1768, k1_zfmisc_1(u1_struct_0(A_1767))) | ~l1_pre_topc(A_1767))), inference(cnfTransformation, [status(thm)], [f_209])).
% 37.69/25.70  tff(c_37159, plain, (u1_struct_0(k1_pre_topc('#skF_3', '#skF_6'))='#skF_6' | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_98, c_37152])).
% 37.69/25.70  tff(c_37167, plain, (u1_struct_0(k1_pre_topc('#skF_3', '#skF_6'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_110, c_37159])).
% 37.69/25.70  tff(c_37171, plain, (~v1_funct_2(k5_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', '#skF_6'), '#skF_6', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_37167, c_3294])).
% 37.69/25.70  tff(c_37059, plain, (![A_1754, B_1755, C_1756]: (k1_relset_1(A_1754, B_1755, C_1756)=k1_relat_1(C_1756) | ~m1_subset_1(C_1756, k1_zfmisc_1(k2_zfmisc_1(A_1754, B_1755))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 37.69/25.70  tff(c_37080, plain, (k1_relset_1(u1_struct_0(k1_pre_topc('#skF_3', '#skF_6')), u1_struct_0('#skF_4'), k5_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', '#skF_6'))=k1_relat_1(k5_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_3295, c_37059])).
% 37.69/25.70  tff(c_69998, plain, (k1_relset_1('#skF_6', u1_struct_0('#skF_4'), k5_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', '#skF_6'))=k1_relat_1(k5_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_37167, c_37080])).
% 37.69/25.70  tff(c_37170, plain, (m1_subset_1(k5_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_6', u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_37167, c_3295])).
% 37.69/25.70  tff(c_70266, plain, (![B_3092, C_3093, A_3094]: (k1_xboole_0=B_3092 | v1_funct_2(C_3093, A_3094, B_3092) | k1_relset_1(A_3094, B_3092, C_3093)!=A_3094 | ~m1_subset_1(C_3093, k1_zfmisc_1(k2_zfmisc_1(A_3094, B_3092))))), inference(cnfTransformation, [status(thm)], [f_176])).
% 37.69/25.70  tff(c_70272, plain, (u1_struct_0('#skF_4')=k1_xboole_0 | v1_funct_2(k5_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', '#skF_6'), '#skF_6', u1_struct_0('#skF_4')) | k1_relset_1('#skF_6', u1_struct_0('#skF_4'), k5_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', '#skF_6'))!='#skF_6'), inference(resolution, [status(thm)], [c_37170, c_70266])).
% 37.69/25.70  tff(c_70296, plain, (u1_struct_0('#skF_4')=k1_xboole_0 | v1_funct_2(k5_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', '#skF_6'), '#skF_6', u1_struct_0('#skF_4')) | k1_relat_1(k5_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', '#skF_6'))!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_69998, c_70272])).
% 37.69/25.70  tff(c_70297, plain, (u1_struct_0('#skF_4')=k1_xboole_0 | k1_relat_1(k5_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', '#skF_6'))!='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_37171, c_70296])).
% 37.69/25.70  tff(c_70363, plain, (k1_relat_1(k5_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', '#skF_6'))!='#skF_6'), inference(splitLeft, [status(thm)], [c_70297])).
% 37.69/25.70  tff(c_74032, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_6'))!='#skF_6' | ~r1_tarski('#skF_5', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_73995, c_70363])).
% 37.69/25.70  tff(c_74087, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_6'))!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_74032])).
% 37.69/25.70  tff(c_78325, plain, (![B_3522, A_3523, A_3524]: (k1_xboole_0=B_3522 | v1_funct_2(A_3523, A_3524, B_3522) | k1_relset_1(A_3524, B_3522, A_3523)!=A_3524 | ~r1_tarski(A_3523, k2_zfmisc_1(A_3524, B_3522)))), inference(resolution, [status(thm)], [c_32, c_70266])).
% 37.69/25.70  tff(c_78357, plain, (![A_3523]: (u1_struct_0('#skF_4')=k1_xboole_0 | v1_funct_2(A_3523, u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | k1_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), A_3523)!=u1_struct_0('#skF_3') | ~r1_tarski(A_3523, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_36502, c_78325])).
% 37.69/25.70  tff(c_78446, plain, (u1_struct_0('#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_78357])).
% 37.69/25.70  tff(c_1696, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_1678])).
% 37.69/25.70  tff(c_40, plain, (![B_31, A_30]: (r1_tarski(k7_relat_1(B_31, A_30), B_31) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_93])).
% 37.69/25.70  tff(c_3355, plain, (![A_467]: (k1_xboole_0=A_467 | ~r1_tarski(A_467, k1_xboole_0))), inference(resolution, [status(thm)], [c_164, c_3333])).
% 37.69/25.70  tff(c_3363, plain, (![A_30]: (k7_relat_1(k1_xboole_0, A_30)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_40, c_3355])).
% 37.69/25.70  tff(c_3375, plain, (![A_30]: (k7_relat_1(k1_xboole_0, A_30)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1696, c_3363])).
% 37.69/25.70  tff(c_36887, plain, (![B_1740, A_1741]: (k1_relat_1(k7_relat_1(B_1740, A_1741))=A_1741 | ~r1_tarski(A_1741, k1_relat_1(B_1740)) | ~v1_relat_1(B_1740))), inference(cnfTransformation, [status(thm)], [f_99])).
% 37.69/25.70  tff(c_36908, plain, (![B_1742]: (k1_relat_1(k7_relat_1(B_1742, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_1742))), inference(resolution, [status(thm)], [c_164, c_36887])).
% 37.69/25.70  tff(c_36921, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3375, c_36908])).
% 37.69/25.70  tff(c_36925, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1696, c_36921])).
% 37.69/25.70  tff(c_37079, plain, (![A_1754, B_1755]: (k1_relset_1(A_1754, B_1755, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_37059])).
% 37.69/25.70  tff(c_37083, plain, (![A_1754, B_1755]: (k1_relset_1(A_1754, B_1755, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36925, c_37079])).
% 37.69/25.70  tff(c_70516, plain, (![C_3103, A_3104, B_3105]: (v1_funct_2(C_3103, A_3104, B_3105) | k1_relset_1(A_3104, B_3105, C_3103)!=A_3104 | ~m1_subset_1(C_3103, k1_zfmisc_1(k2_zfmisc_1(A_3104, B_3105))) | ~v1_funct_1(C_3103))), inference(cnfTransformation, [status(thm)], [f_202])).
% 37.69/25.70  tff(c_70543, plain, (![A_3104, B_3105]: (v1_funct_2(k1_xboole_0, A_3104, B_3105) | k1_relset_1(A_3104, B_3105, k1_xboole_0)!=A_3104 | ~v1_funct_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_70516])).
% 37.69/25.70  tff(c_70554, plain, (![A_3104, B_3105]: (v1_funct_2(k1_xboole_0, A_3104, B_3105) | k1_xboole_0!=A_3104)), inference(demodulation, [status(thm), theory('equality')], [c_181, c_37083, c_70543])).
% 37.69/25.70  tff(c_71353, plain, (![C_3147, A_3148, B_3149]: (~v1_xboole_0(C_3147) | ~v1_funct_2(C_3147, A_3148, B_3149) | ~v1_funct_1(C_3147) | ~m1_subset_1(C_3147, k1_zfmisc_1(k2_zfmisc_1(A_3148, B_3149))) | v1_xboole_0(B_3149) | v1_xboole_0(A_3148))), inference(cnfTransformation, [status(thm)], [f_158])).
% 37.69/25.70  tff(c_71383, plain, (![A_3148, B_3149]: (~v1_xboole_0(k1_xboole_0) | ~v1_funct_2(k1_xboole_0, A_3148, B_3149) | ~v1_funct_1(k1_xboole_0) | v1_xboole_0(B_3149) | v1_xboole_0(A_3148))), inference(resolution, [status(thm)], [c_26, c_71353])).
% 37.69/25.70  tff(c_71398, plain, (![A_3150, B_3151]: (~v1_funct_2(k1_xboole_0, A_3150, B_3151) | v1_xboole_0(B_3151) | v1_xboole_0(A_3150))), inference(demodulation, [status(thm), theory('equality')], [c_181, c_170, c_71383])).
% 37.69/25.70  tff(c_71405, plain, (![B_3105, A_3104]: (v1_xboole_0(B_3105) | v1_xboole_0(A_3104) | k1_xboole_0!=A_3104)), inference(resolution, [status(thm)], [c_70554, c_71398])).
% 37.69/25.70  tff(c_71411, plain, (![A_3152]: (v1_xboole_0(A_3152) | k1_xboole_0!=A_3152)), inference(splitLeft, [status(thm)], [c_71405])).
% 37.69/25.70  tff(c_36639, plain, (v1_xboole_0(k5_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', '#skF_6')) | ~v1_xboole_0(k2_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_3', '#skF_6')), u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_3295, c_28])).
% 37.69/25.70  tff(c_69653, plain, (v1_xboole_0(k5_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', '#skF_6')) | ~v1_xboole_0(k2_zfmisc_1('#skF_6', u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_37167, c_36639])).
% 37.69/25.70  tff(c_69654, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_6', u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_69653])).
% 37.69/25.70  tff(c_71445, plain, (k2_zfmisc_1('#skF_6', u1_struct_0('#skF_4'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_71411, c_69654])).
% 37.69/25.70  tff(c_78478, plain, (k2_zfmisc_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_78446, c_71445])).
% 37.69/25.70  tff(c_78502, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_78478])).
% 37.69/25.70  tff(c_78504, plain, (u1_struct_0('#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_78357])).
% 37.69/25.70  tff(c_71264, plain, (![A_3139, B_3140, A_3141]: (k1_relset_1(A_3139, B_3140, A_3141)=k1_relat_1(A_3141) | ~r1_tarski(A_3141, k2_zfmisc_1(A_3139, B_3140)))), inference(resolution, [status(thm)], [c_32, c_37059])).
% 37.69/25.70  tff(c_71311, plain, (![A_3139, B_3140]: (k1_relset_1(A_3139, B_3140, k2_zfmisc_1(A_3139, B_3140))=k1_relat_1(k2_zfmisc_1(A_3139, B_3140)))), inference(resolution, [status(thm)], [c_16, c_71264])).
% 37.69/25.70  tff(c_70190, plain, (![B_3086, A_3087, C_3088]: (k1_xboole_0=B_3086 | k1_relset_1(A_3087, B_3086, C_3088)=A_3087 | ~v1_funct_2(C_3088, A_3087, B_3086) | ~m1_subset_1(C_3088, k1_zfmisc_1(k2_zfmisc_1(A_3087, B_3086))))), inference(cnfTransformation, [status(thm)], [f_176])).
% 37.69/25.70  tff(c_79549, plain, (![B_3560, A_3561, A_3562]: (k1_xboole_0=B_3560 | k1_relset_1(A_3561, B_3560, A_3562)=A_3561 | ~v1_funct_2(A_3562, A_3561, B_3560) | ~r1_tarski(A_3562, k2_zfmisc_1(A_3561, B_3560)))), inference(resolution, [status(thm)], [c_32, c_70190])).
% 37.69/25.70  tff(c_79603, plain, (![B_3560, A_3561]: (k1_xboole_0=B_3560 | k1_relset_1(A_3561, B_3560, k2_zfmisc_1(A_3561, B_3560))=A_3561 | ~v1_funct_2(k2_zfmisc_1(A_3561, B_3560), A_3561, B_3560))), inference(resolution, [status(thm)], [c_16, c_79549])).
% 37.69/25.70  tff(c_154078, plain, (![B_4289, A_4290]: (k1_xboole_0=B_4289 | k1_relat_1(k2_zfmisc_1(A_4290, B_4289))=A_4290 | ~v1_funct_2(k2_zfmisc_1(A_4290, B_4289), A_4290, B_4289))), inference(demodulation, [status(thm), theory('equality')], [c_71311, c_79603])).
% 37.69/25.70  tff(c_154100, plain, (u1_struct_0('#skF_4')=k1_xboole_0 | k1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))=u1_struct_0('#skF_3') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_36502, c_154078])).
% 37.69/25.70  tff(c_154120, plain, (u1_struct_0('#skF_4')=k1_xboole_0 | u1_struct_0('#skF_3')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_36502, c_154100])).
% 37.69/25.70  tff(c_154121, plain, (u1_struct_0('#skF_3')=k1_relat_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_78504, c_154120])).
% 37.69/25.70  tff(c_154187, plain, (r1_tarski('#skF_6', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_154121, c_163])).
% 37.69/25.70  tff(c_154337, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_6'))='#skF_6' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_154187, c_42])).
% 37.69/25.70  tff(c_154373, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_6'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1695, c_154337])).
% 37.69/25.70  tff(c_154375, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74087, c_154373])).
% 37.69/25.70  tff(c_154376, plain, (![B_3105]: (v1_xboole_0(B_3105))), inference(splitRight, [status(thm)], [c_71405])).
% 37.69/25.70  tff(c_154495, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_154376, c_69654])).
% 37.69/25.70  tff(c_154496, plain, (u1_struct_0('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_70297])).
% 37.69/25.70  tff(c_154501, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_6', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_154496, c_69654])).
% 37.69/25.70  tff(c_154518, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_170, c_22, c_154501])).
% 37.69/25.70  tff(c_154520, plain, (v1_xboole_0(k2_zfmisc_1('#skF_6', u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_69653])).
% 37.69/25.70  tff(c_154565, plain, (k2_zfmisc_1('#skF_6', u1_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_154520, c_180])).
% 37.69/25.70  tff(c_154628, plain, (u1_struct_0('#skF_4')=k1_xboole_0 | k1_xboole_0='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_154565, c_20])).
% 37.69/25.70  tff(c_154631, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_154628])).
% 37.69/25.70  tff(c_154675, plain, (v1_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_154631, c_181])).
% 37.69/25.70  tff(c_154658, plain, (![A_1754, B_1755]: (k1_relset_1(A_1754, B_1755, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_154631, c_154631, c_37083])).
% 37.69/25.70  tff(c_154681, plain, (![A_16]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_16)))), inference(demodulation, [status(thm), theory('equality')], [c_154631, c_26])).
% 37.69/25.70  tff(c_155292, plain, (![C_4324, A_4325, B_4326]: (v1_funct_2(C_4324, A_4325, B_4326) | k1_relset_1(A_4325, B_4326, C_4324)!=A_4325 | ~m1_subset_1(C_4324, k1_zfmisc_1(k2_zfmisc_1(A_4325, B_4326))) | ~v1_funct_1(C_4324))), inference(cnfTransformation, [status(thm)], [f_202])).
% 37.69/25.70  tff(c_155299, plain, (![A_4325, B_4326]: (v1_funct_2('#skF_6', A_4325, B_4326) | k1_relset_1(A_4325, B_4326, '#skF_6')!=A_4325 | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_154681, c_155292])).
% 37.69/25.70  tff(c_155611, plain, (![B_4326]: (v1_funct_2('#skF_6', '#skF_6', B_4326))), inference(demodulation, [status(thm), theory('equality')], [c_154675, c_154658, c_155299])).
% 37.69/25.70  tff(c_154679, plain, (![B_15]: (k2_zfmisc_1('#skF_6', B_15)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_154631, c_154631, c_24])).
% 37.69/25.70  tff(c_69290, plain, (r1_tarski(k5_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', '#skF_6'), k2_zfmisc_1('#skF_6', u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_37170, c_30])).
% 37.69/25.70  tff(c_155179, plain, (r1_tarski(k5_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', '#skF_6'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_154679, c_69290])).
% 37.69/25.70  tff(c_3350, plain, (![A_16]: (k1_xboole_0=A_16 | ~r1_tarski(A_16, k1_xboole_0))), inference(resolution, [status(thm)], [c_164, c_3333])).
% 37.69/25.70  tff(c_155233, plain, (![A_4322]: (A_4322='#skF_6' | ~r1_tarski(A_4322, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_154631, c_154631, c_3350])).
% 37.69/25.70  tff(c_155253, plain, (k5_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', '#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_155179, c_155233])).
% 37.69/25.70  tff(c_155901, plain, (~v1_funct_2('#skF_6', '#skF_6', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_155253, c_37171])).
% 37.69/25.70  tff(c_155912, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_155611, c_155901])).
% 37.69/25.70  tff(c_155913, plain, (u1_struct_0('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_154628])).
% 37.69/25.70  tff(c_155923, plain, (k2_zfmisc_1(u1_struct_0('#skF_3'), k1_xboole_0)='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_155913, c_36502])).
% 37.69/25.70  tff(c_36758, plain, (![A_1721, A_1722, B_1723]: (v4_relat_1(A_1721, A_1722) | ~r1_tarski(A_1721, k2_zfmisc_1(A_1722, B_1723)))), inference(resolution, [status(thm)], [c_32, c_3380])).
% 37.69/25.70  tff(c_36812, plain, (![A_1729, B_1730]: (v4_relat_1(k2_zfmisc_1(A_1729, B_1730), A_1729))), inference(resolution, [status(thm)], [c_16, c_36758])).
% 37.69/25.70  tff(c_38, plain, (![B_29, A_28]: (k7_relat_1(B_29, A_28)=B_29 | ~v4_relat_1(B_29, A_28) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_89])).
% 37.69/25.70  tff(c_36815, plain, (![A_1729, B_1730]: (k7_relat_1(k2_zfmisc_1(A_1729, B_1730), A_1729)=k2_zfmisc_1(A_1729, B_1730) | ~v1_relat_1(k2_zfmisc_1(A_1729, B_1730)))), inference(resolution, [status(thm)], [c_36812, c_38])).
% 37.69/25.70  tff(c_36827, plain, (![A_1729, B_1730]: (k7_relat_1(k2_zfmisc_1(A_1729, B_1730), A_1729)=k2_zfmisc_1(A_1729, B_1730))), inference(demodulation, [status(thm), theory('equality')], [c_1756, c_36815])).
% 37.69/25.70  tff(c_155973, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k2_zfmisc_1(u1_struct_0('#skF_3'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_155923, c_36827])).
% 37.69/25.70  tff(c_156016, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_36577, c_155973])).
% 37.69/25.70  tff(c_156018, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37092, c_156016])).
% 37.69/25.70  tff(c_156020, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_36518])).
% 37.69/25.70  tff(c_156039, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_156020, c_170])).
% 37.69/25.70  tff(c_156048, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36505, c_156039])).
% 37.69/25.70  tff(c_156049, plain, (u1_struct_0('#skF_3')='#skF_6'), inference(splitRight, [status(thm)], [c_3349])).
% 37.69/25.70  tff(c_156058, plain, (v1_funct_2('#skF_5', '#skF_6', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_156049, c_102])).
% 37.69/25.70  tff(c_156051, plain, (v4_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_156049, c_3399])).
% 37.69/25.70  tff(c_156259, plain, (![B_4417, A_4418]: (k7_relat_1(B_4417, A_4418)=B_4417 | ~v4_relat_1(B_4417, A_4418) | ~v1_relat_1(B_4417))), inference(cnfTransformation, [status(thm)], [f_89])).
% 37.69/25.70  tff(c_156274, plain, (k7_relat_1('#skF_5', '#skF_6')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_156051, c_156259])).
% 37.69/25.70  tff(c_156286, plain, (k7_relat_1('#skF_5', '#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1695, c_156274])).
% 37.69/25.70  tff(c_156057, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_6', u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_156049, c_100])).
% 37.69/25.70  tff(c_157491, plain, (![A_4521, B_4522, C_4523, D_4524]: (k5_relset_1(A_4521, B_4522, C_4523, D_4524)=k7_relat_1(C_4523, D_4524) | ~m1_subset_1(C_4523, k1_zfmisc_1(k2_zfmisc_1(A_4521, B_4522))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 37.69/25.70  tff(c_157508, plain, (![D_4524]: (k5_relset_1('#skF_6', u1_struct_0('#skF_4'), '#skF_5', D_4524)=k7_relat_1('#skF_5', D_4524))), inference(resolution, [status(thm)], [c_156057, c_157491])).
% 37.69/25.70  tff(c_156059, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_156049, c_98])).
% 37.69/25.70  tff(c_156971, plain, (![A_4477, B_4478]: (u1_struct_0(k1_pre_topc(A_4477, B_4478))=B_4478 | ~m1_subset_1(B_4478, k1_zfmisc_1(u1_struct_0(A_4477))) | ~l1_pre_topc(A_4477))), inference(cnfTransformation, [status(thm)], [f_209])).
% 37.69/25.70  tff(c_156978, plain, (![B_4478]: (u1_struct_0(k1_pre_topc('#skF_3', B_4478))=B_4478 | ~m1_subset_1(B_4478, k1_zfmisc_1('#skF_6')) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_156049, c_156971])).
% 37.69/25.70  tff(c_157208, plain, (![B_4495]: (u1_struct_0(k1_pre_topc('#skF_3', B_4495))=B_4495 | ~m1_subset_1(B_4495, k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_156978])).
% 37.69/25.70  tff(c_157225, plain, (u1_struct_0(k1_pre_topc('#skF_3', '#skF_6'))='#skF_6'), inference(resolution, [status(thm)], [c_156059, c_157208])).
% 37.69/25.70  tff(c_156586, plain, (~v1_funct_2(k5_relset_1('#skF_6', u1_struct_0('#skF_4'), '#skF_5', '#skF_6'), u1_struct_0(k1_pre_topc('#skF_3', '#skF_6')), u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_156049, c_3294])).
% 37.69/25.70  tff(c_157229, plain, (~v1_funct_2(k5_relset_1('#skF_6', u1_struct_0('#skF_4'), '#skF_5', '#skF_6'), '#skF_6', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_157225, c_156586])).
% 37.69/25.70  tff(c_157521, plain, (~v1_funct_2(k7_relat_1('#skF_5', '#skF_6'), '#skF_6', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_157508, c_157229])).
% 37.69/25.70  tff(c_157527, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_156058, c_156286, c_157521])).
% 37.69/25.70  tff(c_157528, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_208])).
% 37.69/25.70  tff(c_157538, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_157528, c_180])).
% 37.69/25.70  tff(c_70, plain, (![A_60]: (v1_funct_2(k1_xboole_0, A_60, k1_xboole_0) | k1_xboole_0=A_60 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_60, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_176])).
% 37.69/25.70  tff(c_112, plain, (![A_60]: (v1_funct_2(k1_xboole_0, A_60, k1_xboole_0) | k1_xboole_0=A_60)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_70])).
% 37.69/25.70  tff(c_163716, plain, (![A_60]: (v1_funct_2('#skF_5', A_60, '#skF_5') | A_60='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_157538, c_157538, c_157538, c_112])).
% 37.69/25.70  tff(c_163718, plain, (![A_14]: (k2_zfmisc_1(A_14, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_157538, c_157538, c_22])).
% 37.69/25.70  tff(c_163715, plain, (![A_16]: (r1_tarski('#skF_5', A_16))), inference(demodulation, [status(thm), theory('equality')], [c_157538, c_164])).
% 37.69/25.70  tff(c_157529, plain, (v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_208])).
% 37.69/25.70  tff(c_163747, plain, (![A_5099]: (A_5099='#skF_5' | ~v1_xboole_0(A_5099))), inference(resolution, [status(thm)], [c_157528, c_18])).
% 37.69/25.70  tff(c_163754, plain, (k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))='#skF_5'), inference(resolution, [status(thm)], [c_157529, c_163747])).
% 37.69/25.70  tff(c_163945, plain, (![B_5118, A_5119]: (B_5118='#skF_5' | A_5119='#skF_5' | k2_zfmisc_1(A_5119, B_5118)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_157538, c_157538, c_157538, c_20])).
% 37.69/25.70  tff(c_163955, plain, (u1_struct_0('#skF_4')='#skF_5' | u1_struct_0('#skF_3')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_163754, c_163945])).
% 37.69/25.70  tff(c_163960, plain, (u1_struct_0('#skF_3')='#skF_5'), inference(splitLeft, [status(thm)], [c_163955])).
% 37.69/25.70  tff(c_163850, plain, (![B_5109, A_5110]: (B_5109=A_5110 | ~r1_tarski(B_5109, A_5110) | ~r1_tarski(A_5110, B_5109))), inference(cnfTransformation, [status(thm)], [f_44])).
% 37.69/25.70  tff(c_163861, plain, (u1_struct_0('#skF_3')='#skF_6' | ~r1_tarski(u1_struct_0('#skF_3'), '#skF_6')), inference(resolution, [status(thm)], [c_163, c_163850])).
% 37.69/25.70  tff(c_163910, plain, (~r1_tarski(u1_struct_0('#skF_3'), '#skF_6')), inference(splitLeft, [status(thm)], [c_163861])).
% 37.69/25.70  tff(c_163962, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_163960, c_163910])).
% 37.69/25.70  tff(c_163971, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_163715, c_163962])).
% 37.69/25.70  tff(c_163972, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_163955])).
% 37.69/25.70  tff(c_157548, plain, (![A_16]: (r1_tarski('#skF_5', A_16))), inference(demodulation, [status(thm), theory('equality')], [c_157538, c_164])).
% 37.69/25.70  tff(c_157588, plain, (![B_4531, A_4532]: (B_4531=A_4532 | ~r1_tarski(B_4531, A_4532) | ~r1_tarski(A_4532, B_4531))), inference(cnfTransformation, [status(thm)], [f_44])).
% 37.69/25.70  tff(c_157672, plain, (![A_4537]: (A_4537='#skF_5' | ~r1_tarski(A_4537, '#skF_5'))), inference(resolution, [status(thm)], [c_157548, c_157588])).
% 37.69/25.70  tff(c_157680, plain, (![A_30]: (k7_relat_1('#skF_5', A_30)='#skF_5' | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_157672])).
% 37.69/25.70  tff(c_157689, plain, (![A_30]: (k7_relat_1('#skF_5', A_30)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1695, c_157680])).
% 37.69/25.70  tff(c_157552, plain, (![A_16]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_16)))), inference(demodulation, [status(thm), theory('equality')], [c_157538, c_26])).
% 37.69/25.70  tff(c_163683, plain, (![A_5094, B_5095, C_5096, D_5097]: (k5_relset_1(A_5094, B_5095, C_5096, D_5097)=k7_relat_1(C_5096, D_5097) | ~m1_subset_1(C_5096, k1_zfmisc_1(k2_zfmisc_1(A_5094, B_5095))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 37.69/25.70  tff(c_163689, plain, (![A_5094, B_5095, D_5097]: (k5_relset_1(A_5094, B_5095, '#skF_5', D_5097)=k7_relat_1('#skF_5', D_5097))), inference(resolution, [status(thm)], [c_157552, c_163683])).
% 37.69/25.70  tff(c_163699, plain, (![A_5094, B_5095, D_5097]: (k5_relset_1(A_5094, B_5095, '#skF_5', D_5097)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_157689, c_163689])).
% 37.69/25.70  tff(c_161078, plain, (![A_4843, B_4844]: (r2_hidden('#skF_2'(A_4843, B_4844), A_4843) | r1_tarski(A_4843, B_4844))), inference(cnfTransformation, [status(thm)], [f_38])).
% 37.69/25.70  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 37.69/25.70  tff(c_161092, plain, (![A_4843, B_4844]: (~v1_xboole_0(A_4843) | r1_tarski(A_4843, B_4844))), inference(resolution, [status(thm)], [c_161078, c_2])).
% 37.69/25.70  tff(c_157551, plain, (![A_14]: (k2_zfmisc_1(A_14, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_157538, c_157538, c_22])).
% 37.69/25.70  tff(c_160949, plain, (![A_4832, B_4833, C_4834, D_4835]: (k5_relset_1(A_4832, B_4833, C_4834, D_4835)=k7_relat_1(C_4834, D_4835) | ~m1_subset_1(C_4834, k1_zfmisc_1(k2_zfmisc_1(A_4832, B_4833))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 37.69/25.70  tff(c_160955, plain, (![A_4832, B_4833, D_4835]: (k5_relset_1(A_4832, B_4833, '#skF_5', D_4835)=k7_relat_1('#skF_5', D_4835))), inference(resolution, [status(thm)], [c_157552, c_160949])).
% 37.69/25.70  tff(c_160965, plain, (![A_4832, B_4833, D_4835]: (k5_relset_1(A_4832, B_4833, '#skF_5', D_4835)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_157689, c_160955])).
% 37.69/25.70  tff(c_157776, plain, (![A_4550, B_4551]: (r2_hidden('#skF_2'(A_4550, B_4551), A_4550) | r1_tarski(A_4550, B_4551))), inference(cnfTransformation, [status(thm)], [f_38])).
% 37.69/25.70  tff(c_157790, plain, (![A_4550, B_4551]: (~v1_xboole_0(A_4550) | r1_tarski(A_4550, B_4551))), inference(resolution, [status(thm)], [c_157776, c_2])).
% 37.69/25.70  tff(c_157539, plain, (![A_12]: (A_12='#skF_5' | ~v1_xboole_0(A_12))), inference(resolution, [status(thm)], [c_157528, c_18])).
% 37.69/25.70  tff(c_157668, plain, (k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))='#skF_5'), inference(resolution, [status(thm)], [c_157529, c_157539])).
% 37.69/25.70  tff(c_157854, plain, (![B_4557, A_4558]: (B_4557='#skF_5' | A_4558='#skF_5' | k2_zfmisc_1(A_4558, B_4557)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_157538, c_157538, c_157538, c_20])).
% 37.69/25.70  tff(c_157864, plain, (u1_struct_0('#skF_4')='#skF_5' | u1_struct_0('#skF_3')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_157668, c_157854])).
% 37.69/25.70  tff(c_157869, plain, (u1_struct_0('#skF_3')='#skF_5'), inference(splitLeft, [status(thm)], [c_157864])).
% 37.69/25.70  tff(c_157599, plain, (u1_struct_0('#skF_3')='#skF_6' | ~r1_tarski(u1_struct_0('#skF_3'), '#skF_6')), inference(resolution, [status(thm)], [c_163, c_157588])).
% 37.69/25.70  tff(c_157736, plain, (~r1_tarski(u1_struct_0('#skF_3'), '#skF_6')), inference(splitLeft, [status(thm)], [c_157599])).
% 37.69/25.70  tff(c_157870, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_157869, c_157736])).
% 37.69/25.70  tff(c_157879, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_157548, c_157870])).
% 37.69/25.70  tff(c_157880, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_157864])).
% 37.69/25.70  tff(c_157542, plain, (~m1_subset_1(k5_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_3', '#skF_6')), u1_struct_0('#skF_4'))))), inference(splitLeft, [status(thm)], [c_1653])).
% 37.69/25.70  tff(c_157979, plain, (~m1_subset_1(k5_relset_1(u1_struct_0('#skF_3'), '#skF_5', '#skF_5', '#skF_6'), k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_157551, c_157880, c_157880, c_157542])).
% 37.69/25.70  tff(c_157983, plain, (~r1_tarski(k5_relset_1(u1_struct_0('#skF_3'), '#skF_5', '#skF_5', '#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_32, c_157979])).
% 37.69/25.70  tff(c_158057, plain, (~v1_xboole_0(k5_relset_1(u1_struct_0('#skF_3'), '#skF_5', '#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_157790, c_157983])).
% 37.69/25.70  tff(c_160967, plain, (~v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_160965, c_158057])).
% 37.69/25.70  tff(c_160973, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_157528, c_160967])).
% 37.69/25.70  tff(c_160974, plain, (u1_struct_0('#skF_3')='#skF_6'), inference(splitRight, [status(thm)], [c_157599])).
% 37.69/25.70  tff(c_160978, plain, (~v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_160974, c_212])).
% 37.69/25.70  tff(c_160976, plain, (k2_zfmisc_1('#skF_6', u1_struct_0('#skF_4'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_160974, c_157668])).
% 37.69/25.70  tff(c_161005, plain, (![B_4836, A_4837]: (B_4836='#skF_5' | A_4837='#skF_5' | k2_zfmisc_1(A_4837, B_4836)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_157538, c_157538, c_157538, c_20])).
% 37.69/25.70  tff(c_161015, plain, (u1_struct_0('#skF_4')='#skF_5' | '#skF_5'='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_160976, c_161005])).
% 37.69/25.70  tff(c_161020, plain, ('#skF_5'='#skF_6'), inference(splitLeft, [status(thm)], [c_161015])).
% 37.69/25.70  tff(c_161035, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_161020, c_157528])).
% 37.69/25.70  tff(c_161039, plain, $false, inference(negUnitSimplification, [status(thm)], [c_160978, c_161035])).
% 37.69/25.70  tff(c_161040, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_161015])).
% 37.69/25.70  tff(c_161212, plain, (~m1_subset_1(k5_relset_1('#skF_6', '#skF_5', '#skF_5', '#skF_6'), k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_157551, c_161040, c_161040, c_160974, c_157542])).
% 37.69/25.70  tff(c_161216, plain, (~r1_tarski(k5_relset_1('#skF_6', '#skF_5', '#skF_5', '#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_32, c_161212])).
% 37.69/25.70  tff(c_161220, plain, (~v1_xboole_0(k5_relset_1('#skF_6', '#skF_5', '#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_161092, c_161216])).
% 37.69/25.70  tff(c_163701, plain, (~v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_163699, c_161220])).
% 37.69/25.70  tff(c_163707, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_157528, c_163701])).
% 37.69/25.70  tff(c_163709, plain, (m1_subset_1(k5_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_3', '#skF_6')), u1_struct_0('#skF_4'))))), inference(splitRight, [status(thm)], [c_1653])).
% 37.69/25.70  tff(c_164154, plain, (m1_subset_1(k5_relset_1(u1_struct_0('#skF_3'), '#skF_5', '#skF_5', '#skF_6'), k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_163718, c_163972, c_163972, c_163709])).
% 37.69/25.70  tff(c_164163, plain, (v1_xboole_0(k5_relset_1(u1_struct_0('#skF_3'), '#skF_5', '#skF_5', '#skF_6')) | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_164154, c_28])).
% 37.69/25.70  tff(c_164171, plain, (v1_xboole_0(k5_relset_1(u1_struct_0('#skF_3'), '#skF_5', '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_157528, c_164163])).
% 37.69/25.70  tff(c_164210, plain, (k5_relset_1(u1_struct_0('#skF_3'), '#skF_5', '#skF_5', '#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_164171, c_157539])).
% 37.69/25.70  tff(c_163708, plain, (~v1_funct_2(k5_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', '#skF_6'), u1_struct_0(k1_pre_topc('#skF_3', '#skF_6')), u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_1653])).
% 37.69/25.70  tff(c_164071, plain, (~v1_funct_2(k5_relset_1(u1_struct_0('#skF_3'), '#skF_5', '#skF_5', '#skF_6'), u1_struct_0(k1_pre_topc('#skF_3', '#skF_6')), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_163972, c_163972, c_163708])).
% 37.69/25.70  tff(c_164217, plain, (~v1_funct_2('#skF_5', u1_struct_0(k1_pre_topc('#skF_3', '#skF_6')), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_164210, c_164071])).
% 37.69/25.70  tff(c_164237, plain, (u1_struct_0(k1_pre_topc('#skF_3', '#skF_6'))='#skF_5'), inference(resolution, [status(thm)], [c_163716, c_164217])).
% 37.69/25.70  tff(c_164788, plain, (![A_5216, B_5217]: (u1_struct_0(k1_pre_topc(A_5216, B_5217))=B_5217 | ~m1_subset_1(B_5217, k1_zfmisc_1(u1_struct_0(A_5216))) | ~l1_pre_topc(A_5216))), inference(cnfTransformation, [status(thm)], [f_209])).
% 37.69/25.70  tff(c_164805, plain, (u1_struct_0(k1_pre_topc('#skF_3', '#skF_6'))='#skF_6' | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_98, c_164788])).
% 37.69/25.70  tff(c_164812, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_110, c_164237, c_164805])).
% 37.69/25.70  tff(c_163911, plain, (![A_5113, A_5114, B_5115]: (v1_relat_1(A_5113) | ~r1_tarski(A_5113, k2_zfmisc_1(A_5114, B_5115)))), inference(resolution, [status(thm)], [c_32, c_1678])).
% 37.69/25.70  tff(c_163933, plain, (![A_5114, B_5115]: (v1_relat_1(k2_zfmisc_1(A_5114, B_5115)))), inference(resolution, [status(thm)], [c_16, c_163911])).
% 37.69/25.70  tff(c_163717, plain, (![B_15]: (k2_zfmisc_1('#skF_5', B_15)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_157538, c_157538, c_24])).
% 37.69/25.70  tff(c_164123, plain, (![C_5143, A_5144, B_5145]: (v4_relat_1(C_5143, A_5144) | ~m1_subset_1(C_5143, k1_zfmisc_1(k2_zfmisc_1(A_5144, B_5145))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 37.69/25.70  tff(c_164249, plain, (![A_5156, A_5157, B_5158]: (v4_relat_1(A_5156, A_5157) | ~r1_tarski(A_5156, k2_zfmisc_1(A_5157, B_5158)))), inference(resolution, [status(thm)], [c_32, c_164123])).
% 37.69/25.70  tff(c_164278, plain, (![A_5157, B_5158]: (v4_relat_1(k2_zfmisc_1(A_5157, B_5158), A_5157))), inference(resolution, [status(thm)], [c_16, c_164249])).
% 37.69/25.70  tff(c_164378, plain, (![B_5184, A_5185]: (k7_relat_1(B_5184, A_5185)=B_5184 | ~v4_relat_1(B_5184, A_5185) | ~v1_relat_1(B_5184))), inference(cnfTransformation, [status(thm)], [f_89])).
% 37.69/25.70  tff(c_164384, plain, (![A_5157, B_5158]: (k7_relat_1(k2_zfmisc_1(A_5157, B_5158), A_5157)=k2_zfmisc_1(A_5157, B_5158) | ~v1_relat_1(k2_zfmisc_1(A_5157, B_5158)))), inference(resolution, [status(thm)], [c_164278, c_164378])).
% 37.69/25.70  tff(c_164397, plain, (![A_5157, B_5158]: (k7_relat_1(k2_zfmisc_1(A_5157, B_5158), A_5157)=k2_zfmisc_1(A_5157, B_5158))), inference(demodulation, [status(thm), theory('equality')], [c_163933, c_164384])).
% 37.69/25.70  tff(c_164566, plain, (![B_5201, A_5202]: (k1_relat_1(k7_relat_1(B_5201, A_5202))=A_5202 | ~r1_tarski(A_5202, k1_relat_1(B_5201)) | ~v1_relat_1(B_5201))), inference(cnfTransformation, [status(thm)], [f_99])).
% 37.69/25.70  tff(c_164603, plain, (![B_5206]: (k1_relat_1(k7_relat_1(B_5206, '#skF_5'))='#skF_5' | ~v1_relat_1(B_5206))), inference(resolution, [status(thm)], [c_163715, c_164566])).
% 37.69/25.70  tff(c_164616, plain, (![B_5158]: (k1_relat_1(k2_zfmisc_1('#skF_5', B_5158))='#skF_5' | ~v1_relat_1(k2_zfmisc_1('#skF_5', B_5158)))), inference(superposition, [status(thm), theory('equality')], [c_164397, c_164603])).
% 37.69/25.70  tff(c_164624, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_163933, c_163717, c_164616])).
% 37.69/25.70  tff(c_164813, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_164812, c_164812, c_164624])).
% 37.69/25.70  tff(c_163719, plain, (![A_16]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_16)))), inference(demodulation, [status(thm), theory('equality')], [c_157538, c_26])).
% 37.69/25.70  tff(c_165076, plain, (![A_5229]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_5229)))), inference(demodulation, [status(thm), theory('equality')], [c_164812, c_163719])).
% 37.69/25.70  tff(c_165080, plain, (![A_45, B_46]: (k1_relset_1(A_45, B_46, '#skF_6')=k1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_165076, c_58])).
% 37.69/25.70  tff(c_165106, plain, (![A_45, B_46]: (k1_relset_1(A_45, B_46, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_164813, c_165080])).
% 37.69/25.70  tff(c_164840, plain, (![A_16]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_16)))), inference(demodulation, [status(thm), theory('equality')], [c_164812, c_163719])).
% 37.69/25.70  tff(c_164843, plain, (k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_164812, c_157538])).
% 37.69/25.70  tff(c_114, plain, (![C_62, B_61]: (v1_funct_2(C_62, k1_xboole_0, B_61) | k1_relset_1(k1_xboole_0, B_61, C_62)!=k1_xboole_0 | ~m1_subset_1(C_62, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_74])).
% 37.69/25.70  tff(c_165382, plain, (![C_5249, B_5250]: (v1_funct_2(C_5249, '#skF_6', B_5250) | k1_relset_1('#skF_6', B_5250, C_5249)!='#skF_6' | ~m1_subset_1(C_5249, k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_164843, c_164843, c_164843, c_164843, c_114])).
% 37.69/25.70  tff(c_165385, plain, (![B_5250]: (v1_funct_2('#skF_6', '#skF_6', B_5250) | k1_relset_1('#skF_6', B_5250, '#skF_6')!='#skF_6')), inference(resolution, [status(thm)], [c_164840, c_165382])).
% 37.69/25.70  tff(c_165391, plain, (![B_5250]: (v1_funct_2('#skF_6', '#skF_6', B_5250))), inference(demodulation, [status(thm), theory('equality')], [c_165106, c_165385])).
% 37.69/25.70  tff(c_164238, plain, (~v1_funct_2('#skF_5', '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_164237, c_164217])).
% 37.69/25.70  tff(c_164822, plain, (~v1_funct_2('#skF_6', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_164812, c_164812, c_164812, c_164238])).
% 37.69/25.70  tff(c_165395, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_165391, c_164822])).
% 37.69/25.70  tff(c_165396, plain, (u1_struct_0('#skF_3')='#skF_6'), inference(splitRight, [status(thm)], [c_163861])).
% 37.69/25.70  tff(c_165400, plain, (~v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_165396, c_212])).
% 37.69/25.70  tff(c_165398, plain, (k2_zfmisc_1('#skF_6', u1_struct_0('#skF_4'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_165396, c_163754])).
% 37.69/25.70  tff(c_165529, plain, (![B_5265, A_5266]: (B_5265='#skF_5' | A_5266='#skF_5' | k2_zfmisc_1(A_5266, B_5265)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_157538, c_157538, c_157538, c_20])).
% 37.69/25.70  tff(c_165539, plain, (u1_struct_0('#skF_4')='#skF_5' | '#skF_5'='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_165398, c_165529])).
% 37.69/25.70  tff(c_165544, plain, ('#skF_5'='#skF_6'), inference(splitLeft, [status(thm)], [c_165539])).
% 37.69/25.70  tff(c_165581, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_165544, c_157528])).
% 37.69/25.70  tff(c_165585, plain, $false, inference(negUnitSimplification, [status(thm)], [c_165400, c_165581])).
% 37.69/25.70  tff(c_165587, plain, ('#skF_5'!='#skF_6'), inference(splitRight, [status(thm)], [c_165539])).
% 37.69/25.70  tff(c_165403, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_165396, c_98])).
% 37.69/25.70  tff(c_166213, plain, (![A_5349, B_5350]: (u1_struct_0(k1_pre_topc(A_5349, B_5350))=B_5350 | ~m1_subset_1(B_5350, k1_zfmisc_1(u1_struct_0(A_5349))) | ~l1_pre_topc(A_5349))), inference(cnfTransformation, [status(thm)], [f_209])).
% 37.69/25.70  tff(c_166222, plain, (![B_5350]: (u1_struct_0(k1_pre_topc('#skF_3', B_5350))=B_5350 | ~m1_subset_1(B_5350, k1_zfmisc_1('#skF_6')) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_165396, c_166213])).
% 37.69/25.70  tff(c_166368, plain, (![B_5358]: (u1_struct_0(k1_pre_topc('#skF_3', B_5358))=B_5358 | ~m1_subset_1(B_5358, k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_166222])).
% 37.69/25.70  tff(c_166385, plain, (u1_struct_0(k1_pre_topc('#skF_3', '#skF_6'))='#skF_6'), inference(resolution, [status(thm)], [c_165403, c_166368])).
% 37.69/25.70  tff(c_165586, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_165539])).
% 37.69/25.70  tff(c_165662, plain, (m1_subset_1(k5_relset_1('#skF_6', '#skF_5', '#skF_5', '#skF_6'), k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_163718, c_165586, c_165586, c_165396, c_163709])).
% 37.69/25.70  tff(c_165668, plain, (v1_xboole_0(k5_relset_1('#skF_6', '#skF_5', '#skF_5', '#skF_6')) | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_165662, c_28])).
% 37.69/25.70  tff(c_165675, plain, (v1_xboole_0(k5_relset_1('#skF_6', '#skF_5', '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_157528, c_165668])).
% 37.69/25.70  tff(c_165700, plain, (k5_relset_1('#skF_6', '#skF_5', '#skF_5', '#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_165675, c_157539])).
% 37.69/25.70  tff(c_165503, plain, (~v1_funct_2(k5_relset_1('#skF_6', u1_struct_0('#skF_4'), '#skF_5', '#skF_6'), u1_struct_0(k1_pre_topc('#skF_3', '#skF_6')), u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_165396, c_163708])).
% 37.69/25.70  tff(c_165588, plain, (~v1_funct_2(k5_relset_1('#skF_6', '#skF_5', '#skF_5', '#skF_6'), u1_struct_0(k1_pre_topc('#skF_3', '#skF_6')), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_165586, c_165586, c_165503])).
% 37.69/25.70  tff(c_165747, plain, (~v1_funct_2('#skF_5', u1_struct_0(k1_pre_topc('#skF_3', '#skF_6')), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_165700, c_165588])).
% 37.69/25.70  tff(c_165751, plain, (u1_struct_0(k1_pre_topc('#skF_3', '#skF_6'))='#skF_5'), inference(resolution, [status(thm)], [c_163716, c_165747])).
% 37.69/25.70  tff(c_166388, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_166385, c_165751])).
% 37.69/25.70  tff(c_166390, plain, $false, inference(negUnitSimplification, [status(thm)], [c_165587, c_166388])).
% 37.69/25.70  tff(c_166391, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_209])).
% 37.69/25.70  tff(c_166401, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_166391, c_180])).
% 37.69/25.70  tff(c_166410, plain, (![B_15]: (k2_zfmisc_1('#skF_6', B_15)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_166401, c_166401, c_24])).
% 37.69/25.70  tff(c_166392, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_209])).
% 37.69/25.70  tff(c_168965, plain, (![A_5597]: (A_5597='#skF_6' | ~v1_xboole_0(A_5597))), inference(resolution, [status(thm)], [c_166391, c_18])).
% 37.69/25.70  tff(c_168972, plain, (u1_struct_0('#skF_3')='#skF_6'), inference(resolution, [status(thm)], [c_166392, c_168965])).
% 37.69/25.70  tff(c_168978, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_6', u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_168972, c_174])).
% 37.69/25.70  tff(c_169049, plain, (r1_tarski('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_166410, c_168978])).
% 37.69/25.70  tff(c_169100, plain, (![A_5610, B_5611]: (v1_xboole_0(A_5610) | ~v1_xboole_0(B_5611) | ~r1_tarski(A_5610, B_5611))), inference(resolution, [status(thm)], [c_32, c_194])).
% 37.69/25.70  tff(c_169103, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_169049, c_169100])).
% 37.69/25.70  tff(c_169115, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_166391, c_169103])).
% 37.69/25.70  tff(c_166402, plain, (![A_12]: (A_12='#skF_6' | ~v1_xboole_0(A_12))), inference(resolution, [status(thm)], [c_166391, c_18])).
% 37.69/25.70  tff(c_169145, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_169115, c_166402])).
% 37.69/25.70  tff(c_168980, plain, (v1_funct_2('#skF_5', '#skF_6', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_168972, c_102])).
% 37.69/25.70  tff(c_169154, plain, (v1_funct_2('#skF_6', '#skF_6', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_169145, c_168980])).
% 37.69/25.70  tff(c_166412, plain, (![A_16]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_16)))), inference(demodulation, [status(thm), theory('equality')], [c_166401, c_26])).
% 37.69/25.70  tff(c_173045, plain, (![A_5977, B_5978]: (u1_struct_0(k1_pre_topc(A_5977, B_5978))=B_5978 | ~m1_subset_1(B_5978, k1_zfmisc_1(u1_struct_0(A_5977))) | ~l1_pre_topc(A_5977))), inference(cnfTransformation, [status(thm)], [f_209])).
% 37.69/25.70  tff(c_173057, plain, (![A_5977]: (u1_struct_0(k1_pre_topc(A_5977, '#skF_6'))='#skF_6' | ~l1_pre_topc(A_5977))), inference(resolution, [status(thm)], [c_166412, c_173045])).
% 37.69/25.70  tff(c_173061, plain, (![A_5979]: (u1_struct_0(k1_pre_topc(A_5979, '#skF_6'))='#skF_6' | ~l1_pre_topc(A_5979))), inference(resolution, [status(thm)], [c_166412, c_173045])).
% 37.69/25.70  tff(c_169018, plain, (![C_5600, A_5601, B_5602]: (v1_relat_1(C_5600) | ~m1_subset_1(C_5600, k1_zfmisc_1(k2_zfmisc_1(A_5601, B_5602))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 37.69/25.70  tff(c_169029, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_166412, c_169018])).
% 37.69/25.70  tff(c_166408, plain, (![A_16]: (r1_tarski('#skF_6', A_16))), inference(demodulation, [status(thm), theory('equality')], [c_166401, c_164])).
% 37.69/25.70  tff(c_169240, plain, (![B_5626, A_5627]: (B_5626=A_5627 | ~r1_tarski(B_5626, A_5627) | ~r1_tarski(A_5627, B_5626))), inference(cnfTransformation, [status(thm)], [f_44])).
% 37.69/25.70  tff(c_169256, plain, (![A_5628]: (A_5628='#skF_6' | ~r1_tarski(A_5628, '#skF_6'))), inference(resolution, [status(thm)], [c_166408, c_169240])).
% 37.69/25.70  tff(c_169268, plain, (![A_30]: (k7_relat_1('#skF_6', A_30)='#skF_6' | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_40, c_169256])).
% 37.69/25.70  tff(c_169278, plain, (![A_30]: (k7_relat_1('#skF_6', A_30)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_169029, c_169268])).
% 37.69/25.70  tff(c_172379, plain, (![A_5893, B_5894, C_5895, D_5896]: (k5_relset_1(A_5893, B_5894, C_5895, D_5896)=k7_relat_1(C_5895, D_5896) | ~m1_subset_1(C_5895, k1_zfmisc_1(k2_zfmisc_1(A_5893, B_5894))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 37.69/25.70  tff(c_172392, plain, (![A_5893, B_5894, D_5896]: (k5_relset_1(A_5893, B_5894, '#skF_6', D_5896)=k7_relat_1('#skF_6', D_5896))), inference(resolution, [status(thm)], [c_166412, c_172379])).
% 37.69/25.70  tff(c_172399, plain, (![A_5893, B_5894, D_5896]: (k5_relset_1(A_5893, B_5894, '#skF_6', D_5896)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_169278, c_172392])).
% 37.69/25.70  tff(c_169977, plain, (![A_5715, B_5716]: (u1_struct_0(k1_pre_topc(A_5715, B_5716))=B_5716 | ~m1_subset_1(B_5716, k1_zfmisc_1(u1_struct_0(A_5715))) | ~l1_pre_topc(A_5715))), inference(cnfTransformation, [status(thm)], [f_209])).
% 37.69/25.70  tff(c_169988, plain, (![B_5716]: (u1_struct_0(k1_pre_topc('#skF_3', B_5716))=B_5716 | ~m1_subset_1(B_5716, k1_zfmisc_1('#skF_6')) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_168972, c_169977])).
% 37.69/25.70  tff(c_170045, plain, (![B_5720]: (u1_struct_0(k1_pre_topc('#skF_3', B_5720))=B_5720 | ~m1_subset_1(B_5720, k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_169988])).
% 37.69/25.70  tff(c_170059, plain, (u1_struct_0(k1_pre_topc('#skF_3', '#skF_6'))='#skF_6'), inference(resolution, [status(thm)], [c_166412, c_170045])).
% 37.69/25.70  tff(c_166403, plain, (v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_166391, c_44])).
% 37.69/25.70  tff(c_166501, plain, (![A_5368]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_5368)))), inference(demodulation, [status(thm), theory('equality')], [c_166401, c_26])).
% 37.69/25.70  tff(c_52, plain, (![C_41, A_39, B_40]: (v1_relat_1(C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 37.69/25.70  tff(c_166512, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_166501, c_52])).
% 37.69/25.70  tff(c_166687, plain, (![B_5387, A_5388]: (B_5387=A_5388 | ~r1_tarski(B_5387, A_5388) | ~r1_tarski(A_5388, B_5387))), inference(cnfTransformation, [status(thm)], [f_44])).
% 37.69/25.70  tff(c_166703, plain, (![A_5389]: (A_5389='#skF_6' | ~r1_tarski(A_5389, '#skF_6'))), inference(resolution, [status(thm)], [c_166408, c_166687])).
% 37.69/25.70  tff(c_166715, plain, (![A_30]: (k7_relat_1('#skF_6', A_30)='#skF_6' | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_40, c_166703])).
% 37.69/25.70  tff(c_166725, plain, (![A_30]: (k7_relat_1('#skF_6', A_30)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_166512, c_166715])).
% 37.69/25.70  tff(c_168931, plain, (![A_5592, B_5593, C_5594, D_5595]: (k5_relset_1(A_5592, B_5593, C_5594, D_5595)=k7_relat_1(C_5594, D_5595) | ~m1_subset_1(C_5594, k1_zfmisc_1(k2_zfmisc_1(A_5592, B_5593))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 37.69/25.70  tff(c_168937, plain, (![A_5592, B_5593, D_5595]: (k5_relset_1(A_5592, B_5593, '#skF_6', D_5595)=k7_relat_1('#skF_6', D_5595))), inference(resolution, [status(thm)], [c_166412, c_168931])).
% 37.69/25.70  tff(c_168947, plain, (![A_5592, B_5593, D_5595]: (k5_relset_1(A_5592, B_5593, '#skF_6', D_5595)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_166725, c_168937])).
% 37.69/25.70  tff(c_166435, plain, (![A_5362]: (A_5362='#skF_6' | ~v1_xboole_0(A_5362))), inference(resolution, [status(thm)], [c_166391, c_18])).
% 37.69/25.70  tff(c_166442, plain, (u1_struct_0('#skF_3')='#skF_6'), inference(resolution, [status(thm)], [c_166392, c_166435])).
% 37.69/25.70  tff(c_166448, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_6', u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_166442, c_100])).
% 37.69/25.70  tff(c_166582, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_166410, c_166448])).
% 37.69/25.70  tff(c_166588, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_166582, c_28])).
% 37.69/25.70  tff(c_166596, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_166391, c_166588])).
% 37.69/25.70  tff(c_166607, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_166596, c_166402])).
% 37.69/25.70  tff(c_166426, plain, (~v1_funct_1(k5_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_96])).
% 37.69/25.70  tff(c_166661, plain, (~v1_funct_1(k5_relset_1('#skF_6', u1_struct_0('#skF_4'), '#skF_6', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_166607, c_166442, c_166426])).
% 37.69/25.70  tff(c_168951, plain, (~v1_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_168947, c_166661])).
% 37.69/25.70  tff(c_168954, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_166403, c_168951])).
% 37.69/25.70  tff(c_168955, plain, (~v1_funct_2(k5_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', '#skF_6'), u1_struct_0(k1_pre_topc('#skF_3', '#skF_6')), u1_struct_0('#skF_4')) | ~m1_subset_1(k5_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_3', '#skF_6')), u1_struct_0('#skF_4'))))), inference(splitRight, [status(thm)], [c_96])).
% 37.69/25.70  tff(c_169323, plain, (~v1_funct_2(k5_relset_1('#skF_6', u1_struct_0('#skF_4'), '#skF_6', '#skF_6'), u1_struct_0(k1_pre_topc('#skF_3', '#skF_6')), u1_struct_0('#skF_4')) | ~m1_subset_1(k5_relset_1('#skF_6', u1_struct_0('#skF_4'), '#skF_6', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_3', '#skF_6')), u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_169145, c_168972, c_169145, c_168972, c_168955])).
% 37.69/25.70  tff(c_169324, plain, (~m1_subset_1(k5_relset_1('#skF_6', u1_struct_0('#skF_4'), '#skF_6', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_3', '#skF_6')), u1_struct_0('#skF_4'))))), inference(splitLeft, [status(thm)], [c_169323])).
% 37.69/25.70  tff(c_170087, plain, (~m1_subset_1(k5_relset_1('#skF_6', u1_struct_0('#skF_4'), '#skF_6', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_6', u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_170059, c_169324])).
% 37.69/25.70  tff(c_170089, plain, (~m1_subset_1(k5_relset_1('#skF_6', u1_struct_0('#skF_4'), '#skF_6', '#skF_6'), k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_166410, c_170087])).
% 37.69/25.70  tff(c_172401, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_172399, c_170089])).
% 37.69/25.70  tff(c_172407, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_166412, c_172401])).
% 37.69/25.70  tff(c_172409, plain, (m1_subset_1(k5_relset_1('#skF_6', u1_struct_0('#skF_4'), '#skF_6', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_3', '#skF_6')), u1_struct_0('#skF_4'))))), inference(splitRight, [status(thm)], [c_169323])).
% 37.69/25.70  tff(c_172526, plain, (r1_tarski(k5_relset_1('#skF_6', u1_struct_0('#skF_4'), '#skF_6', '#skF_6'), k2_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_3', '#skF_6')), u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_172409, c_30])).
% 37.69/25.70  tff(c_173070, plain, (r1_tarski(k5_relset_1('#skF_6', u1_struct_0('#skF_4'), '#skF_6', '#skF_6'), k2_zfmisc_1('#skF_6', u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_173061, c_172526])).
% 37.69/25.70  tff(c_173085, plain, (r1_tarski(k5_relset_1('#skF_6', u1_struct_0('#skF_4'), '#skF_6', '#skF_6'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_166410, c_173070])).
% 37.69/25.70  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 37.69/25.70  tff(c_172490, plain, (![C_5912, B_5913, A_5914]: (r2_hidden(C_5912, B_5913) | ~r2_hidden(C_5912, A_5914) | ~r1_tarski(A_5914, B_5913))), inference(cnfTransformation, [status(thm)], [f_38])).
% 37.69/25.70  tff(c_172789, plain, (![A_5961, B_5962]: (r2_hidden('#skF_1'(A_5961), B_5962) | ~r1_tarski(A_5961, B_5962) | v1_xboole_0(A_5961))), inference(resolution, [status(thm)], [c_4, c_172490])).
% 37.69/25.70  tff(c_172999, plain, (![B_5974, A_5975]: (~r1_tarski(B_5974, '#skF_1'(A_5975)) | ~r1_tarski(A_5975, B_5974) | v1_xboole_0(A_5975))), inference(resolution, [status(thm)], [c_172789, c_50])).
% 37.69/25.70  tff(c_173017, plain, (![A_5975]: (~r1_tarski(A_5975, '#skF_6') | v1_xboole_0(A_5975))), inference(resolution, [status(thm)], [c_166408, c_172999])).
% 37.69/25.70  tff(c_173110, plain, (v1_xboole_0(k5_relset_1('#skF_6', u1_struct_0('#skF_4'), '#skF_6', '#skF_6'))), inference(resolution, [status(thm)], [c_173085, c_173017])).
% 37.69/25.70  tff(c_173146, plain, (k5_relset_1('#skF_6', u1_struct_0('#skF_4'), '#skF_6', '#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_173110, c_166402])).
% 37.69/25.70  tff(c_172408, plain, (~v1_funct_2(k5_relset_1('#skF_6', u1_struct_0('#skF_4'), '#skF_6', '#skF_6'), u1_struct_0(k1_pre_topc('#skF_3', '#skF_6')), u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_169323])).
% 37.69/25.70  tff(c_173157, plain, (~v1_funct_2('#skF_6', u1_struct_0(k1_pre_topc('#skF_3', '#skF_6')), u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_173146, c_172408])).
% 37.69/25.70  tff(c_173186, plain, (~v1_funct_2('#skF_6', '#skF_6', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_173057, c_173157])).
% 37.69/25.70  tff(c_173189, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_110, c_169154, c_173186])).
% 37.69/25.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 37.69/25.70  
% 37.69/25.70  Inference rules
% 37.69/25.70  ----------------------
% 37.69/25.70  #Ref     : 42
% 37.69/25.70  #Sup     : 41791
% 37.69/25.70  #Fact    : 0
% 37.69/25.70  #Define  : 0
% 37.69/25.70  #Split   : 143
% 37.69/25.70  #Chain   : 0
% 37.69/25.70  #Close   : 0
% 37.69/25.70  
% 37.69/25.70  Ordering : KBO
% 37.69/25.70  
% 37.69/25.70  Simplification rules
% 37.69/25.70  ----------------------
% 37.69/25.70  #Subsume      : 16739
% 37.69/25.70  #Demod        : 28990
% 37.69/25.70  #Tautology    : 13232
% 37.69/25.70  #SimpNegUnit  : 1712
% 37.69/25.70  #BackRed      : 2283
% 37.69/25.70  
% 37.69/25.70  #Partial instantiations: 0
% 37.69/25.70  #Strategies tried      : 1
% 37.69/25.70  
% 37.69/25.70  Timing (in seconds)
% 37.69/25.70  ----------------------
% 37.77/25.70  Preprocessing        : 0.43
% 37.77/25.70  Parsing              : 0.23
% 37.77/25.70  CNF conversion       : 0.03
% 37.77/25.70  Main loop            : 24.32
% 37.77/25.70  Inferencing          : 4.00
% 37.77/25.70  Reduction            : 10.31
% 37.77/25.70  Demodulation         : 8.13
% 37.77/25.70  BG Simplification    : 0.35
% 37.77/25.70  Subsumption          : 8.31
% 37.77/25.70  Abstraction          : 0.58
% 37.77/25.70  MUC search           : 0.00
% 37.77/25.70  Cooper               : 0.00
% 37.77/25.70  Total                : 24.92
% 37.77/25.70  Index Insertion      : 0.00
% 37.77/25.70  Index Deletion       : 0.00
% 37.77/25.70  Index Matching       : 0.00
% 37.77/25.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
