%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1240+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:38 EST 2020

% Result     : Theorem 55.76s
% Output     : CNFRefutation 56.14s
% Verified   : 
% Statistics : Number of formulae       :  286 (2636 expanded)
%              Number of leaves         :   39 ( 894 expanded)
%              Depth                    :   17
%              Number of atoms          :  683 (8005 expanded)
%              Number of equality atoms :   53 (1004 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_162,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B,C] :
            ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
           => ( r2_hidden(B,k1_tops_1(A,C))
            <=> ? [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                  & v3_pre_topc(D,A)
                  & r1_tarski(D,C)
                  & r2_hidden(B,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_tops_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_143,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(f_78,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & v3_pre_topc(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_tops_1)).

tff(f_131,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_110,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k2_pre_topc(A,B),k2_pre_topc(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_116,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_50,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_138,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(c_46,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_44,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_181669,plain,(
    ! [A_4081,B_4082] :
      ( v3_pre_topc(k1_tops_1(A_4081,B_4082),A_4081)
      | ~ m1_subset_1(B_4082,k1_zfmisc_1(u1_struct_0(A_4081)))
      | ~ l1_pre_topc(A_4081)
      | ~ v2_pre_topc(A_4081) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_181677,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_181669])).

tff(c_181685,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_181677])).

tff(c_181536,plain,(
    ! [A_4066,B_4067] :
      ( r1_tarski(k1_tops_1(A_4066,B_4067),B_4067)
      | ~ m1_subset_1(B_4067,k1_zfmisc_1(u1_struct_0(A_4066)))
      | ~ l1_pre_topc(A_4066) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_181544,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_181536])).

tff(c_181552,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_181544])).

tff(c_178333,plain,(
    ! [A_3875,B_3876] :
      ( v3_pre_topc(k1_tops_1(A_3875,B_3876),A_3875)
      | ~ m1_subset_1(B_3876,k1_zfmisc_1(u1_struct_0(A_3875)))
      | ~ l1_pre_topc(A_3875)
      | ~ v2_pre_topc(A_3875) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_178348,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_178333])).

tff(c_178359,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_178348])).

tff(c_178046,plain,(
    ! [A_3843,B_3844] :
      ( r1_tarski(k1_tops_1(A_3843,B_3844),B_3844)
      | ~ m1_subset_1(B_3844,k1_zfmisc_1(u1_struct_0(A_3843)))
      | ~ l1_pre_topc(A_3843) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_178054,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_178046])).

tff(c_178062,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_178054])).

tff(c_174566,plain,(
    ! [A_3637,B_3638] :
      ( v3_pre_topc(k1_tops_1(A_3637,B_3638),A_3637)
      | ~ m1_subset_1(B_3638,k1_zfmisc_1(u1_struct_0(A_3637)))
      | ~ l1_pre_topc(A_3637)
      | ~ v2_pre_topc(A_3637) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_174574,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_174566])).

tff(c_174582,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_174574])).

tff(c_174489,plain,(
    ! [A_3628,B_3629] :
      ( r1_tarski(k1_tops_1(A_3628,B_3629),B_3629)
      | ~ m1_subset_1(B_3629,k1_zfmisc_1(u1_struct_0(A_3628)))
      | ~ l1_pre_topc(A_3628) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_174497,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_174489])).

tff(c_174505,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_174497])).

tff(c_171199,plain,(
    ! [A_3419,B_3420] :
      ( v3_pre_topc(k1_tops_1(A_3419,B_3420),A_3419)
      | ~ m1_subset_1(B_3420,k1_zfmisc_1(u1_struct_0(A_3419)))
      | ~ l1_pre_topc(A_3419)
      | ~ v2_pre_topc(A_3419) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_171207,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_171199])).

tff(c_171215,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_171207])).

tff(c_171087,plain,(
    ! [A_3404,B_3405] :
      ( r1_tarski(k1_tops_1(A_3404,B_3405),B_3405)
      | ~ m1_subset_1(B_3405,k1_zfmisc_1(u1_struct_0(A_3404)))
      | ~ l1_pre_topc(A_3404) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_171095,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_171087])).

tff(c_171103,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_171095])).

tff(c_62,plain,
    ( r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | v3_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_85,plain,(
    v3_pre_topc('#skF_5','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_58,plain,
    ( r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | r1_tarski('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_96,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_54,plain,
    ( r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | r2_hidden('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_91,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_66,plain,
    ( r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_109,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_40,plain,(
    ! [B_46,A_45] :
      ( ~ v1_xboole_0(B_46)
      | ~ r2_hidden(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_95,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_91,c_40])).

tff(c_18,plain,(
    ! [A_18,B_19] :
      ( r2_hidden(A_18,B_19)
      | v1_xboole_0(B_19)
      | ~ m1_subset_1(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_48,plain,(
    ! [D_55] :
      ( ~ r2_hidden('#skF_3',D_55)
      | ~ r1_tarski(D_55,'#skF_4')
      | ~ v3_pre_topc(D_55,'#skF_2')
      | ~ m1_subset_1(D_55,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_543,plain,(
    ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_547,plain,
    ( v1_xboole_0(k1_tops_1('#skF_2','#skF_4'))
    | ~ m1_subset_1('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_18,c_543])).

tff(c_548,plain,(
    ~ m1_subset_1('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_547])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(k3_subset_1(A_8,B_9),k1_zfmisc_1(A_8))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_130,plain,(
    ! [A_74,B_75] :
      ( k3_subset_1(A_74,k3_subset_1(A_74,B_75)) = B_75
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_142,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_42,c_130])).

tff(c_54143,plain,(
    ! [A_1267,C_1268,B_1269] :
      ( r1_tarski(k3_subset_1(A_1267,C_1268),k3_subset_1(A_1267,B_1269))
      | ~ r1_tarski(B_1269,C_1268)
      | ~ m1_subset_1(C_1268,k1_zfmisc_1(A_1267))
      | ~ m1_subset_1(B_1269,k1_zfmisc_1(A_1267)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_54174,plain,(
    ! [B_1269] :
      ( r1_tarski('#skF_4',k3_subset_1(u1_struct_0('#skF_2'),B_1269))
      | ~ r1_tarski(B_1269,k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_1269,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_54143])).

tff(c_54402,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_54174])).

tff(c_54463,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_8,c_54402])).

tff(c_54470,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_54463])).

tff(c_54472,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_54174])).

tff(c_140,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_109,c_130])).

tff(c_54591,plain,(
    ! [B_1296,C_1297,A_1298] :
      ( r1_tarski(B_1296,C_1297)
      | ~ r1_tarski(k3_subset_1(A_1298,C_1297),k3_subset_1(A_1298,B_1296))
      | ~ m1_subset_1(C_1297,k1_zfmisc_1(A_1298))
      | ~ m1_subset_1(B_1296,k1_zfmisc_1(A_1298)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_54621,plain,(
    ! [B_1296] :
      ( r1_tarski(B_1296,k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'))
      | ~ r1_tarski('#skF_4',k3_subset_1(u1_struct_0('#skF_2'),B_1296))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_1296,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_54591])).

tff(c_54971,plain,(
    ! [B_1315] :
      ( r1_tarski(B_1315,k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'))
      | ~ r1_tarski('#skF_4',k3_subset_1(u1_struct_0('#skF_2'),B_1315))
      | ~ m1_subset_1(B_1315,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54472,c_54621])).

tff(c_54987,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'))
    | ~ r1_tarski('#skF_4','#skF_5')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_54971])).

tff(c_55240,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_54987])).

tff(c_55243,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_8,c_55240])).

tff(c_55250,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_55243])).

tff(c_55252,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_54987])).

tff(c_54615,plain,(
    ! [B_1296] :
      ( r1_tarski(B_1296,k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'))
      | ~ r1_tarski('#skF_5',k3_subset_1(u1_struct_0('#skF_2'),B_1296))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_1296,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_54591])).

tff(c_55368,plain,(
    ! [B_1339] :
      ( r1_tarski(B_1339,k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'))
      | ~ r1_tarski('#skF_5',k3_subset_1(u1_struct_0('#skF_2'),B_1339))
      | ~ m1_subset_1(B_1339,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55252,c_54615])).

tff(c_55386,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'))
    | ~ r1_tarski('#skF_5','#skF_4')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_55368])).

tff(c_55392,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54472,c_96,c_55386])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_12),B_13),A_12)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ v3_pre_topc(B_13,A_12)
      | ~ l1_pre_topc(A_12)
      | ~ v2_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_34,plain,(
    ! [B_41,A_39] :
      ( v4_pre_topc(B_41,A_39)
      | k2_pre_topc(A_39,B_41) != B_41
      | ~ v2_pre_topc(A_39)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_55264,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),'#skF_2')
    | k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')) != k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')
    | ~ v2_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_55252,c_34])).

tff(c_55292,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),'#skF_2')
    | k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')) != k3_subset_1(u1_struct_0('#skF_2'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_55264])).

tff(c_58041,plain,(
    k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')) != k3_subset_1(u1_struct_0('#skF_2'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_55292])).

tff(c_36,plain,(
    ! [A_39,B_41] :
      ( k2_pre_topc(A_39,B_41) = B_41
      | ~ v4_pre_topc(B_41,A_39)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_55267,plain,
    ( k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_55252,c_36])).

tff(c_55295,plain,
    ( k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_55267])).

tff(c_58642,plain,(
    ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_58041,c_55295])).

tff(c_58645,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ v3_pre_topc('#skF_5','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_58642])).

tff(c_58649,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_85,c_109,c_58645])).

tff(c_58651,plain,(
    k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_55292])).

tff(c_30,plain,(
    ! [A_29,B_33,C_35] :
      ( r1_tarski(k2_pre_topc(A_29,B_33),k2_pre_topc(A_29,C_35))
      | ~ r1_tarski(B_33,C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ l1_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_58672,plain,(
    ! [B_33] :
      ( r1_tarski(k2_pre_topc('#skF_2',B_33),k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'))
      | ~ r1_tarski(B_33,k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58651,c_30])).

tff(c_58699,plain,(
    ! [B_33] :
      ( r1_tarski(k2_pre_topc('#skF_2',B_33),k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'))
      | ~ r1_tarski(B_33,k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_55252,c_58672])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(k2_pre_topc(A_6,B_7),k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(k1_tops_1(A_4,B_5),k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_54100,plain,(
    ! [B_1265,A_1266] :
      ( v4_pre_topc(B_1265,A_1266)
      | k2_pre_topc(A_1266,B_1265) != B_1265
      | ~ v2_pre_topc(A_1266)
      | ~ m1_subset_1(B_1265,k1_zfmisc_1(u1_struct_0(A_1266)))
      | ~ l1_pre_topc(A_1266) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_61099,plain,(
    ! [A_1472,B_1473] :
      ( v4_pre_topc(k1_tops_1(A_1472,B_1473),A_1472)
      | k2_pre_topc(A_1472,k1_tops_1(A_1472,B_1473)) != k1_tops_1(A_1472,B_1473)
      | ~ v2_pre_topc(A_1472)
      | ~ m1_subset_1(B_1473,k1_zfmisc_1(u1_struct_0(A_1472)))
      | ~ l1_pre_topc(A_1472) ) ),
    inference(resolution,[status(thm)],[c_4,c_54100])).

tff(c_61132,plain,
    ( v4_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')) != k1_tops_1('#skF_2','#skF_4')
    | ~ v2_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_61099])).

tff(c_61164,plain,
    ( v4_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')) != k1_tops_1('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_61132])).

tff(c_61276,plain,(
    k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')) != k1_tops_1('#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_61164])).

tff(c_24,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(A_24,B_25)
      | ~ m1_subset_1(A_24,k1_zfmisc_1(B_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_54571,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_54472,c_24])).

tff(c_26,plain,(
    ! [A_24,B_25] :
      ( m1_subset_1(A_24,k1_zfmisc_1(B_25))
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_141,plain,(
    ! [B_25,A_24] :
      ( k3_subset_1(B_25,k3_subset_1(B_25,A_24)) = A_24
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(resolution,[status(thm)],[c_26,c_130])).

tff(c_54759,plain,(
    ! [A_1306,B_1307] :
      ( k3_subset_1(u1_struct_0(A_1306),k2_pre_topc(A_1306,k3_subset_1(u1_struct_0(A_1306),B_1307))) = k1_tops_1(A_1306,B_1307)
      | ~ m1_subset_1(B_1307,k1_zfmisc_1(u1_struct_0(A_1306)))
      | ~ l1_pre_topc(A_1306) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_95479,plain,(
    ! [A_2075,A_2076] :
      ( k3_subset_1(u1_struct_0(A_2075),k2_pre_topc(A_2075,A_2076)) = k1_tops_1(A_2075,k3_subset_1(u1_struct_0(A_2075),A_2076))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_2075),A_2076),k1_zfmisc_1(u1_struct_0(A_2075)))
      | ~ l1_pre_topc(A_2075)
      | ~ r1_tarski(A_2076,u1_struct_0(A_2075)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_54759])).

tff(c_95543,plain,
    ( k3_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'))) = k1_tops_1('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ r1_tarski(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_95479])).

tff(c_95577,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'))) = k1_tops_1('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54571,c_44,c_42,c_142,c_95543])).

tff(c_50930,plain,(
    ! [A_1113,B_1114] :
      ( k2_pre_topc(A_1113,B_1114) = B_1114
      | ~ v4_pre_topc(B_1114,A_1113)
      | ~ m1_subset_1(B_1114,k1_zfmisc_1(u1_struct_0(A_1113)))
      | ~ l1_pre_topc(A_1113) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_50958,plain,(
    ! [A_1113,B_9] :
      ( k2_pre_topc(A_1113,k3_subset_1(u1_struct_0(A_1113),B_9)) = k3_subset_1(u1_struct_0(A_1113),B_9)
      | ~ v4_pre_topc(k3_subset_1(u1_struct_0(A_1113),B_9),A_1113)
      | ~ l1_pre_topc(A_1113)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(u1_struct_0(A_1113))) ) ),
    inference(resolution,[status(thm)],[c_8,c_50930])).

tff(c_95707,plain,
    ( k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')))) = k3_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')))
    | ~ v4_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ m1_subset_1(k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_95577,c_50958])).

tff(c_95833,plain,
    ( k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')) = k1_tops_1('#skF_2','#skF_4')
    | ~ v4_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ m1_subset_1(k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_95577,c_95577,c_95707])).

tff(c_95834,plain,
    ( ~ v4_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ m1_subset_1(k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_61276,c_95833])).

tff(c_96334,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_95834])).

tff(c_96337,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_96334])).

tff(c_96344,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_54472,c_96337])).

tff(c_96346,plain,(
    m1_subset_1(k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_95834])).

tff(c_55367,plain,(
    ! [B_1296] :
      ( r1_tarski(B_1296,k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'))
      | ~ r1_tarski('#skF_5',k3_subset_1(u1_struct_0('#skF_2'),B_1296))
      | ~ m1_subset_1(B_1296,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55252,c_54615])).

tff(c_95729,plain,
    ( r1_tarski(k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')),k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'))
    | ~ r1_tarski('#skF_5',k1_tops_1('#skF_2','#skF_4'))
    | ~ m1_subset_1(k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_95577,c_55367])).

tff(c_121704,plain,
    ( r1_tarski(k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')),k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'))
    | ~ r1_tarski('#skF_5',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96346,c_95729])).

tff(c_121705,plain,(
    ~ r1_tarski('#skF_5',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_121704])).

tff(c_95775,plain,
    ( m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1(k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_95577,c_8])).

tff(c_96925,plain,(
    m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96346,c_95775])).

tff(c_480,plain,(
    ! [A_120,B_121] :
      ( m1_subset_1(k2_pre_topc(A_120,B_121),k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ l1_pre_topc(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [A_16,B_17] :
      ( k3_subset_1(A_16,k3_subset_1(A_16,B_17)) = B_17
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_497,plain,(
    ! [A_120,B_121] :
      ( k3_subset_1(u1_struct_0(A_120),k3_subset_1(u1_struct_0(A_120),k2_pre_topc(A_120,B_121))) = k2_pre_topc(A_120,B_121)
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ l1_pre_topc(A_120) ) ),
    inference(resolution,[status(thm)],[c_480,c_16])).

tff(c_95710,plain,
    ( k3_subset_1(u1_struct_0('#skF_2'),k1_tops_1('#skF_2','#skF_4')) = k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_95577,c_497])).

tff(c_95836,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),k1_tops_1('#skF_2','#skF_4')) = k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_54472,c_95710])).

tff(c_57671,plain,(
    ! [A_1410,B_1411] :
      ( k3_subset_1(u1_struct_0(A_1410),k3_subset_1(u1_struct_0(A_1410),k2_pre_topc(A_1410,B_1411))) = k2_pre_topc(A_1410,B_1411)
      | ~ m1_subset_1(B_1411,k1_zfmisc_1(u1_struct_0(A_1410)))
      | ~ l1_pre_topc(A_1410) ) ),
    inference(resolution,[status(thm)],[c_480,c_16])).

tff(c_20,plain,(
    ! [B_21,C_23,A_20] :
      ( r1_tarski(B_21,C_23)
      | ~ r1_tarski(k3_subset_1(A_20,C_23),k3_subset_1(A_20,B_21))
      | ~ m1_subset_1(C_23,k1_zfmisc_1(A_20))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_125165,plain,(
    ! [A_2449,B_2450,C_2451] :
      ( r1_tarski(k3_subset_1(u1_struct_0(A_2449),k2_pre_topc(A_2449,B_2450)),C_2451)
      | ~ r1_tarski(k3_subset_1(u1_struct_0(A_2449),C_2451),k2_pre_topc(A_2449,B_2450))
      | ~ m1_subset_1(C_2451,k1_zfmisc_1(u1_struct_0(A_2449)))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_2449),k2_pre_topc(A_2449,B_2450)),k1_zfmisc_1(u1_struct_0(A_2449)))
      | ~ m1_subset_1(B_2450,k1_zfmisc_1(u1_struct_0(A_2449)))
      | ~ l1_pre_topc(A_2449) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57671,c_20])).

tff(c_125214,plain,(
    ! [C_2451] :
      ( r1_tarski(k3_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'))),C_2451)
      | ~ r1_tarski(k3_subset_1(u1_struct_0('#skF_2'),C_2451),k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'))
      | ~ m1_subset_1(C_2451,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'))),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58651,c_125165])).

tff(c_125292,plain,(
    ! [C_2452] :
      ( r1_tarski('#skF_5',C_2452)
      | ~ r1_tarski(k3_subset_1(u1_struct_0('#skF_2'),C_2452),k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'))
      | ~ m1_subset_1(C_2452,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_55252,c_109,c_140,c_58651,c_140,c_58651,c_125214])).

tff(c_125317,plain,
    ( r1_tarski('#skF_5',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')),k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'))
    | ~ m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_95836,c_125292])).

tff(c_125419,plain,
    ( r1_tarski('#skF_5',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')),k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96925,c_125317])).

tff(c_125420,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')),k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_121705,c_125419])).

tff(c_125480,plain,
    ( ~ r1_tarski(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_58699,c_125420])).

tff(c_125484,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54472,c_55392,c_125480])).

tff(c_125486,plain,(
    r1_tarski('#skF_5',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_121704])).

tff(c_211,plain,(
    ! [A_79,C_80,B_81] :
      ( m1_subset_1(A_79,C_80)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(C_80))
      | ~ r2_hidden(A_79,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_258,plain,(
    ! [A_88,B_89,A_90] :
      ( m1_subset_1(A_88,B_89)
      | ~ r2_hidden(A_88,A_90)
      | ~ r1_tarski(A_90,B_89) ) ),
    inference(resolution,[status(thm)],[c_26,c_211])).

tff(c_263,plain,(
    ! [B_89] :
      ( m1_subset_1('#skF_3',B_89)
      | ~ r1_tarski('#skF_5',B_89) ) ),
    inference(resolution,[status(thm)],[c_91,c_258])).

tff(c_125499,plain,(
    m1_subset_1('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_125486,c_263])).

tff(c_125517,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_548,c_125499])).

tff(c_125518,plain,(
    v1_xboole_0(k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_547])).

tff(c_128627,plain,(
    ! [A_2607,C_2608,B_2609] :
      ( r1_tarski(k3_subset_1(A_2607,C_2608),k3_subset_1(A_2607,B_2609))
      | ~ r1_tarski(B_2609,C_2608)
      | ~ m1_subset_1(C_2608,k1_zfmisc_1(A_2607))
      | ~ m1_subset_1(B_2609,k1_zfmisc_1(A_2607)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_128658,plain,(
    ! [B_2609] :
      ( r1_tarski('#skF_4',k3_subset_1(u1_struct_0('#skF_2'),B_2609))
      | ~ r1_tarski(B_2609,k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_2609,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_128627])).

tff(c_128939,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_128658])).

tff(c_128942,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_8,c_128939])).

tff(c_128949,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_128942])).

tff(c_128951,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_128658])).

tff(c_129018,plain,(
    ! [B_2632,C_2633,A_2634] :
      ( r1_tarski(B_2632,C_2633)
      | ~ r1_tarski(k3_subset_1(A_2634,C_2633),k3_subset_1(A_2634,B_2632))
      | ~ m1_subset_1(C_2633,k1_zfmisc_1(A_2634))
      | ~ m1_subset_1(B_2632,k1_zfmisc_1(A_2634)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_129048,plain,(
    ! [B_2632] :
      ( r1_tarski(B_2632,k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'))
      | ~ r1_tarski('#skF_4',k3_subset_1(u1_struct_0('#skF_2'),B_2632))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_2632,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_129018])).

tff(c_129611,plain,(
    ! [B_2664] :
      ( r1_tarski(B_2664,k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'))
      | ~ r1_tarski('#skF_4',k3_subset_1(u1_struct_0('#skF_2'),B_2664))
      | ~ m1_subset_1(B_2664,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128951,c_129048])).

tff(c_129627,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'))
    | ~ r1_tarski('#skF_4','#skF_5')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_129611])).

tff(c_129661,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_129627])).

tff(c_129664,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_8,c_129661])).

tff(c_129671,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_129664])).

tff(c_129673,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_129627])).

tff(c_129042,plain,(
    ! [B_2632] :
      ( r1_tarski(B_2632,k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'))
      | ~ r1_tarski('#skF_5',k3_subset_1(u1_struct_0('#skF_2'),B_2632))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_2632,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_129018])).

tff(c_129844,plain,(
    ! [B_2681] :
      ( r1_tarski(B_2681,k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'))
      | ~ r1_tarski('#skF_5',k3_subset_1(u1_struct_0('#skF_2'),B_2681))
      | ~ m1_subset_1(B_2681,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129673,c_129042])).

tff(c_129862,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'))
    | ~ r1_tarski('#skF_5','#skF_4')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_129844])).

tff(c_129868,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128951,c_96,c_129862])).

tff(c_129688,plain,
    ( k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_129673,c_36])).

tff(c_129716,plain,
    ( k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_129688])).

tff(c_132559,plain,(
    ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_129716])).

tff(c_132562,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ v3_pre_topc('#skF_5','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_132559])).

tff(c_132566,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_85,c_109,c_132562])).

tff(c_132567,plain,(
    k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_129716])).

tff(c_132680,plain,(
    ! [B_33] :
      ( r1_tarski(k2_pre_topc('#skF_2',B_33),k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'))
      | ~ r1_tarski(B_33,k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132567,c_30])).

tff(c_132709,plain,(
    ! [B_33] :
      ( r1_tarski(k2_pre_topc('#skF_2',B_33),k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'))
      | ~ r1_tarski(B_33,k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_129673,c_132680])).

tff(c_128579,plain,(
    ! [B_2602,A_2603] :
      ( v4_pre_topc(B_2602,A_2603)
      | k2_pre_topc(A_2603,B_2602) != B_2602
      | ~ v2_pre_topc(A_2603)
      | ~ m1_subset_1(B_2602,k1_zfmisc_1(u1_struct_0(A_2603)))
      | ~ l1_pre_topc(A_2603) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_135514,plain,(
    ! [A_2809,B_2810] :
      ( v4_pre_topc(k1_tops_1(A_2809,B_2810),A_2809)
      | k2_pre_topc(A_2809,k1_tops_1(A_2809,B_2810)) != k1_tops_1(A_2809,B_2810)
      | ~ v2_pre_topc(A_2809)
      | ~ m1_subset_1(B_2810,k1_zfmisc_1(u1_struct_0(A_2809)))
      | ~ l1_pre_topc(A_2809) ) ),
    inference(resolution,[status(thm)],[c_4,c_128579])).

tff(c_135549,plain,
    ( v4_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')) != k1_tops_1('#skF_2','#skF_4')
    | ~ v2_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_135514])).

tff(c_135584,plain,
    ( v4_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')) != k1_tops_1('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_135549])).

tff(c_135640,plain,(
    k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')) != k1_tops_1('#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_135584])).

tff(c_128992,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_128951,c_24])).

tff(c_129222,plain,(
    ! [A_2643,B_2644] :
      ( k3_subset_1(u1_struct_0(A_2643),k2_pre_topc(A_2643,k3_subset_1(u1_struct_0(A_2643),B_2644))) = k1_tops_1(A_2643,B_2644)
      | ~ m1_subset_1(B_2644,k1_zfmisc_1(u1_struct_0(A_2643)))
      | ~ l1_pre_topc(A_2643) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_149475,plain,(
    ! [A_3114,A_3115] :
      ( k3_subset_1(u1_struct_0(A_3114),k2_pre_topc(A_3114,A_3115)) = k1_tops_1(A_3114,k3_subset_1(u1_struct_0(A_3114),A_3115))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_3114),A_3115),k1_zfmisc_1(u1_struct_0(A_3114)))
      | ~ l1_pre_topc(A_3114)
      | ~ r1_tarski(A_3115,u1_struct_0(A_3114)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_129222])).

tff(c_149539,plain,
    ( k3_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'))) = k1_tops_1('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ r1_tarski(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_149475])).

tff(c_149573,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'))) = k1_tops_1('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128992,c_44,c_42,c_142,c_149539])).

tff(c_128400,plain,(
    ! [A_2594,B_2595] :
      ( k2_pre_topc(A_2594,B_2595) = B_2595
      | ~ v4_pre_topc(B_2595,A_2594)
      | ~ m1_subset_1(B_2595,k1_zfmisc_1(u1_struct_0(A_2594)))
      | ~ l1_pre_topc(A_2594) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_128432,plain,(
    ! [A_2594,B_9] :
      ( k2_pre_topc(A_2594,k3_subset_1(u1_struct_0(A_2594),B_9)) = k3_subset_1(u1_struct_0(A_2594),B_9)
      | ~ v4_pre_topc(k3_subset_1(u1_struct_0(A_2594),B_9),A_2594)
      | ~ l1_pre_topc(A_2594)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(u1_struct_0(A_2594))) ) ),
    inference(resolution,[status(thm)],[c_8,c_128400])).

tff(c_149733,plain,
    ( k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')))) = k3_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')))
    | ~ v4_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ m1_subset_1(k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_149573,c_128432])).

tff(c_149876,plain,
    ( k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')) = k1_tops_1('#skF_2','#skF_4')
    | ~ v4_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ m1_subset_1(k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_149573,c_149573,c_149733])).

tff(c_149877,plain,
    ( ~ v4_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ m1_subset_1(k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_135640,c_149876])).

tff(c_150570,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_149877])).

tff(c_150573,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_150570])).

tff(c_150580,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_128951,c_150573])).

tff(c_150582,plain,(
    m1_subset_1(k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_149877])).

tff(c_129843,plain,(
    ! [B_2632] :
      ( r1_tarski(B_2632,k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'))
      | ~ r1_tarski('#skF_5',k3_subset_1(u1_struct_0('#skF_2'),B_2632))
      | ~ m1_subset_1(B_2632,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129673,c_129042])).

tff(c_149755,plain,
    ( r1_tarski(k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')),k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'))
    | ~ r1_tarski('#skF_5',k1_tops_1('#skF_2','#skF_4'))
    | ~ m1_subset_1(k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_149573,c_129843])).

tff(c_159265,plain,
    ( r1_tarski(k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')),k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'))
    | ~ r1_tarski('#skF_5',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_150582,c_149755])).

tff(c_159266,plain,(
    ~ r1_tarski('#skF_5',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_159265])).

tff(c_149801,plain,
    ( m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1(k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_149573,c_8])).

tff(c_151196,plain,(
    m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_150582,c_149801])).

tff(c_149736,plain,
    ( k3_subset_1(u1_struct_0('#skF_2'),k1_tops_1('#skF_2','#skF_4')) = k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_149573,c_497])).

tff(c_149879,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),k1_tops_1('#skF_2','#skF_4')) = k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_128951,c_149736])).

tff(c_132310,plain,(
    ! [A_2745,B_2746] :
      ( k3_subset_1(u1_struct_0(A_2745),k3_subset_1(u1_struct_0(A_2745),k2_pre_topc(A_2745,B_2746))) = k2_pre_topc(A_2745,B_2746)
      | ~ m1_subset_1(B_2746,k1_zfmisc_1(u1_struct_0(A_2745)))
      | ~ l1_pre_topc(A_2745) ) ),
    inference(resolution,[status(thm)],[c_480,c_16])).

tff(c_170474,plain,(
    ! [A_3370,B_3371,C_3372] :
      ( r1_tarski(k3_subset_1(u1_struct_0(A_3370),k2_pre_topc(A_3370,B_3371)),C_3372)
      | ~ r1_tarski(k3_subset_1(u1_struct_0(A_3370),C_3372),k2_pre_topc(A_3370,B_3371))
      | ~ m1_subset_1(C_3372,k1_zfmisc_1(u1_struct_0(A_3370)))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_3370),k2_pre_topc(A_3370,B_3371)),k1_zfmisc_1(u1_struct_0(A_3370)))
      | ~ m1_subset_1(B_3371,k1_zfmisc_1(u1_struct_0(A_3370)))
      | ~ l1_pre_topc(A_3370) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132310,c_20])).

tff(c_170521,plain,(
    ! [C_3372] :
      ( r1_tarski(k3_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'))),C_3372)
      | ~ r1_tarski(k3_subset_1(u1_struct_0('#skF_2'),C_3372),k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'))
      | ~ m1_subset_1(C_3372,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'))),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132567,c_170474])).

tff(c_170601,plain,(
    ! [C_3373] :
      ( r1_tarski('#skF_5',C_3373)
      | ~ r1_tarski(k3_subset_1(u1_struct_0('#skF_2'),C_3373),k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'))
      | ~ m1_subset_1(C_3373,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_129673,c_109,c_140,c_132567,c_140,c_132567,c_170521])).

tff(c_170626,plain,
    ( r1_tarski('#skF_5',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')),k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'))
    | ~ m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_149879,c_170601])).

tff(c_170728,plain,
    ( r1_tarski('#skF_5',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')),k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_151196,c_170626])).

tff(c_170729,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')),k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_159266,c_170728])).

tff(c_170790,plain,
    ( ~ r1_tarski(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_132709,c_170729])).

tff(c_170794,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_128951,c_129868,c_170790])).

tff(c_170796,plain,(
    r1_tarski('#skF_5',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_159265])).

tff(c_227,plain,(
    ! [A_84,B_85] :
      ( m1_subset_1(k3_subset_1(A_84,B_85),k1_zfmisc_1(A_84))
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_249,plain,(
    ! [A_84,B_85] :
      ( r1_tarski(k3_subset_1(A_84,B_85),A_84)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_84)) ) ),
    inference(resolution,[status(thm)],[c_227,c_24])).

tff(c_10,plain,(
    ! [A_10] : m1_subset_1('#skF_1'(A_10),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_38,plain,(
    ! [C_44,B_43,A_42] :
      ( ~ v1_xboole_0(C_44)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(C_44))
      | ~ r2_hidden(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_369,plain,(
    ! [A_100,A_101,B_102] :
      ( ~ v1_xboole_0(A_100)
      | ~ r2_hidden(A_101,k3_subset_1(A_100,B_102))
      | ~ m1_subset_1(B_102,k1_zfmisc_1(A_100)) ) ),
    inference(resolution,[status(thm)],[c_227,c_38])).

tff(c_128712,plain,(
    ! [A_2615,B_2616,A_2617] :
      ( ~ v1_xboole_0(A_2615)
      | ~ m1_subset_1(B_2616,k1_zfmisc_1(A_2615))
      | v1_xboole_0(k3_subset_1(A_2615,B_2616))
      | ~ m1_subset_1(A_2617,k3_subset_1(A_2615,B_2616)) ) ),
    inference(resolution,[status(thm)],[c_18,c_369])).

tff(c_128739,plain,(
    ! [B_2618,A_2619,A_2620] :
      ( ~ v1_xboole_0(B_2618)
      | v1_xboole_0(k3_subset_1(B_2618,A_2619))
      | ~ m1_subset_1(A_2620,k3_subset_1(B_2618,A_2619))
      | ~ r1_tarski(A_2619,B_2618) ) ),
    inference(resolution,[status(thm)],[c_26,c_128712])).

tff(c_128769,plain,(
    ! [B_2621,A_2622] :
      ( ~ v1_xboole_0(B_2621)
      | v1_xboole_0(k3_subset_1(B_2621,A_2622))
      | ~ r1_tarski(A_2622,B_2621) ) ),
    inference(resolution,[status(thm)],[c_10,c_128739])).

tff(c_128812,plain,(
    ! [B_2625,A_2626] :
      ( ~ v1_xboole_0(B_2625)
      | v1_xboole_0(A_2626)
      | ~ r1_tarski(k3_subset_1(B_2625,A_2626),B_2625)
      | ~ r1_tarski(A_2626,B_2625) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_128769])).

tff(c_128838,plain,(
    ! [A_2627,B_2628] :
      ( ~ v1_xboole_0(A_2627)
      | v1_xboole_0(B_2628)
      | ~ r1_tarski(B_2628,A_2627)
      | ~ m1_subset_1(B_2628,k1_zfmisc_1(A_2627)) ) ),
    inference(resolution,[status(thm)],[c_249,c_128812])).

tff(c_128873,plain,(
    ! [B_25,A_24] :
      ( ~ v1_xboole_0(B_25)
      | v1_xboole_0(A_24)
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(resolution,[status(thm)],[c_26,c_128838])).

tff(c_170804,plain,
    ( ~ v1_xboole_0(k1_tops_1('#skF_2','#skF_4'))
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_170796,c_128873])).

tff(c_170818,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125518,c_170804])).

tff(c_170820,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_170818])).

tff(c_170872,plain,(
    ! [D_3376] :
      ( ~ r2_hidden('#skF_3',D_3376)
      | ~ r1_tarski(D_3376,'#skF_4')
      | ~ v3_pre_topc(D_3376,'#skF_2')
      | ~ m1_subset_1(D_3376,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_170887,plain,
    ( ~ r2_hidden('#skF_3','#skF_5')
    | ~ r1_tarski('#skF_5','#skF_4')
    | ~ v3_pre_topc('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_109,c_170872])).

tff(c_170907,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_96,c_91,c_170887])).

tff(c_170908,plain,(
    r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_171466,plain,(
    ! [A_3446,B_3447] :
      ( m1_subset_1(k1_tops_1(A_3446,B_3447),k1_zfmisc_1(u1_struct_0(A_3446)))
      | ~ m1_subset_1(B_3447,k1_zfmisc_1(u1_struct_0(A_3446)))
      | ~ l1_pre_topc(A_3446) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_170909,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_64,plain,(
    ! [D_55] :
      ( ~ r2_hidden('#skF_3',D_55)
      | ~ r1_tarski(D_55,'#skF_4')
      | ~ v3_pre_topc(D_55,'#skF_2')
      | ~ m1_subset_1(D_55,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_171223,plain,(
    ! [D_55] :
      ( ~ r2_hidden('#skF_3',D_55)
      | ~ r1_tarski(D_55,'#skF_4')
      | ~ v3_pre_topc(D_55,'#skF_2')
      | ~ m1_subset_1(D_55,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_170909,c_64])).

tff(c_171473,plain,(
    ! [B_3447] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_3447))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_3447),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_3447),'#skF_2')
      | ~ m1_subset_1(B_3447,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_171466,c_171223])).

tff(c_174194,plain,(
    ! [B_3590] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_3590))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_3590),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_3590),'#skF_2')
      | ~ m1_subset_1(B_3590,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_171473])).

tff(c_174234,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_174194])).

tff(c_174262,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_171215,c_171103,c_170908,c_174234])).

tff(c_174263,plain,(
    r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_174736,plain,(
    ! [A_3658,B_3659] :
      ( m1_subset_1(k1_tops_1(A_3658,B_3659),k1_zfmisc_1(u1_struct_0(A_3658)))
      | ~ m1_subset_1(B_3659,k1_zfmisc_1(u1_struct_0(A_3658)))
      | ~ l1_pre_topc(A_3658) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_174264,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_56,plain,(
    ! [D_55] :
      ( ~ r2_hidden('#skF_3',D_55)
      | ~ r1_tarski(D_55,'#skF_4')
      | ~ v3_pre_topc(D_55,'#skF_2')
      | ~ m1_subset_1(D_55,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | r1_tarski('#skF_5','#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_174309,plain,(
    ! [D_55] :
      ( ~ r2_hidden('#skF_3',D_55)
      | ~ r1_tarski(D_55,'#skF_4')
      | ~ v3_pre_topc(D_55,'#skF_2')
      | ~ m1_subset_1(D_55,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_174264,c_56])).

tff(c_174748,plain,(
    ! [B_3659] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_3659))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_3659),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_3659),'#skF_2')
      | ~ m1_subset_1(B_3659,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_174736,c_174309])).

tff(c_177769,plain,(
    ! [B_3810] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_3810))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_3810),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_3810),'#skF_2')
      | ~ m1_subset_1(B_3810,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_174748])).

tff(c_177809,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_177769])).

tff(c_177837,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_174582,c_174505,c_174263,c_177809])).

tff(c_177838,plain,(
    r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_178228,plain,(
    ! [A_3866,B_3867] :
      ( m1_subset_1(k1_tops_1(A_3866,B_3867),k1_zfmisc_1(u1_struct_0(A_3866)))
      | ~ m1_subset_1(B_3867,k1_zfmisc_1(u1_struct_0(A_3866)))
      | ~ l1_pre_topc(A_3866) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_177839,plain,(
    ~ r2_hidden('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_52,plain,(
    ! [D_55] :
      ( ~ r2_hidden('#skF_3',D_55)
      | ~ r1_tarski(D_55,'#skF_4')
      | ~ v3_pre_topc(D_55,'#skF_2')
      | ~ m1_subset_1(D_55,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | r2_hidden('#skF_3','#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_177877,plain,(
    ! [D_55] :
      ( ~ r2_hidden('#skF_3',D_55)
      | ~ r1_tarski(D_55,'#skF_4')
      | ~ v3_pre_topc(D_55,'#skF_2')
      | ~ m1_subset_1(D_55,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_177839,c_52])).

tff(c_178238,plain,(
    ! [B_3867] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_3867))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_3867),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_3867),'#skF_2')
      | ~ m1_subset_1(B_3867,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_178228,c_177877])).

tff(c_181253,plain,(
    ! [B_4026] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_4026))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_4026),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_4026),'#skF_2')
      | ~ m1_subset_1(B_4026,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_178238])).

tff(c_181293,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_181253])).

tff(c_181321,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_178359,c_178062,c_177838,c_181293])).

tff(c_181322,plain,(
    r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_181755,plain,(
    ! [A_4091,B_4092] :
      ( m1_subset_1(k1_tops_1(A_4091,B_4092),k1_zfmisc_1(u1_struct_0(A_4091)))
      | ~ m1_subset_1(B_4092,k1_zfmisc_1(u1_struct_0(A_4091)))
      | ~ l1_pre_topc(A_4091) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_181323,plain,(
    ~ v3_pre_topc('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_60,plain,(
    ! [D_55] :
      ( ~ r2_hidden('#skF_3',D_55)
      | ~ r1_tarski(D_55,'#skF_4')
      | ~ v3_pre_topc(D_55,'#skF_2')
      | ~ m1_subset_1(D_55,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v3_pre_topc('#skF_5','#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_181572,plain,(
    ! [D_55] :
      ( ~ r2_hidden('#skF_3',D_55)
      | ~ r1_tarski(D_55,'#skF_4')
      | ~ v3_pre_topc(D_55,'#skF_2')
      | ~ m1_subset_1(D_55,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_181323,c_60])).

tff(c_181764,plain,(
    ! [B_4092] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_4092))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_4092),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_4092),'#skF_2')
      | ~ m1_subset_1(B_4092,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_181755,c_181572])).

tff(c_184109,plain,(
    ! [B_4211] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_4211))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_4211),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_4211),'#skF_2')
      | ~ m1_subset_1(B_4211,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_181764])).

tff(c_184146,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_184109])).

tff(c_184171,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_181685,c_181552,c_181322,c_184146])).

%------------------------------------------------------------------------------
